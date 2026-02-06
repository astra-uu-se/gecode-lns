// fzn-pbs.cpp

// Includes
#include <iostream>
#include <fstream>
#include <gecode/flatzinc.hh>
#include <gecode/flatzinc/registry.hh>
#include <gecode/flatzinc/plugin.hh>
#include <gecode/flatzinc/branch.hh>
#include <gecode/search.hh>
#include <gecode/flatzinc/fzn-pbs.hh>
#include <gecode/flatzinc/searchenginebase.hh>
#include <gecode/flatzinc/branchmodifier.hh>
#include <gecode/flatzinc/lnsstrategies.hh>

#include <array>
#include <vector>
#include <string>
#include <sstream>
#include <limits>
#include <unordered_set>
#include <bits/random.h>
#include <random>

using namespace std;
using namespace Gecode;
using namespace Gecode::FlatZinc;

SearchController::SearchController(FlatZinc::FlatZincSpace* flatZincSpace, std::ostream& out, Printer& printer, FlatZincOptions& flatZincOptions, Support::Timer& timerTotal)
    : _flatZincSpace(flatZincSpace),
      _ostream(out),
      _printer(printer),
      _flatZincOptions(flatZincOptions),
      _timerTotal(timerTotal),
      _method(flatZincSpace->method()),
      _runningThreads(std::atomic<int>{0}),
      _allBestSolutions(std::make_shared<std::vector<std::shared_ptr<Space>>>()) {
    assert(!_flatZincSpace->useSoftSubsume());
}

SearchController::~SearchController() = default;

void SearchController::thread_done() {
    if (_runningThreads.fetch_sub(1) == 1) {
        _executionDoneEvent.signal();
    }
}

FlatZincSpace::AssetType SearchController::assetType(size_t armId, bool lockMutex) {
    if (lockMutex) {
        _banditMutex.lock();
    }
    const auto assetType = armId < _armIdToAssetType.size()
        ? _armIdToAssetType[armId]
        : FlatZincSpace::AssetType::DUMMY;
    if (lockMutex) {
        _banditMutex.unlock();
    }
    return assetType;
}

bool SearchController::useSelfSubsumingPropagators(size_t armId, bool lock) {
    if (lock) {
        _banditMutex.lock();
    }
    const auto assetType = armId < _armIdToSelfSubsuming.size()
        ? _armIdToSelfSubsuming[armId]
        : false;
    if (lock) {
        _banditMutex.unlock();
    }
    return assetType;
}

bool SearchController::useDependencyCuratedLns(size_t armId, bool lock) {
    if (lock) {
        _banditMutex.lock();
    }
    const auto assetType = armId < _armIdToSelfSubsuming.size()
        ? _armIdToCuratedDependency[armId]
        : false;
    if (lock) {
        _banditMutex.unlock();
    }
    return assetType;
}

bool SearchController::updateBestSolution(const std::shared_ptr<FlatZincSpace> &sol,
                                          unsigned int asset_id) {
    // If the optimum was found, then stop there is no need to update the best solution.
    for (const auto& intVar : sol->iv) {
        assert(intVar.assigned());
    }

    _solutionMutex.lock();
    if (_optimumFound->load()) {
        _solutionMutex.unlock();
        return false;
    }

    const auto expected = _flatZincSpace->_incumbentSolution->load();
    const int sol_comp = expected == nullptr ? -1 : sol->compareObjectiveValue(*expected);
    if (sol_comp <= 0) {
        // Critical Section
        const bool success = sol_comp < 0
            ? _flatZincSpace->_incumbentSolution->compare_replace_strong(expected, sol)
            : _flatZincSpace->_incumbentSolution->compare_enqueue_strong(expected, sol);
        assert(success);

        if (_method != FlatZincSpace::SAT &&
            (expected == nullptr || !expected->viol_vars.empty() && expected->total_viol.val() > 0) &&
            (sol->viol_vars.empty() || sol->total_viol.val() == 0)) {
            _ostream << "%% Violation: " << sol->total_viol << std::endl;
            _ostream << "%% allowing hard constraint assets" << std::endl;
            if (sol->optVarIsInt() && sol->optVar() >= 0) {
                _ostream << "%% objective: " << sol->iv[sol->optVar()] << std::endl;
            }
            updateMultiArmedBandit();
        } else if (sol_comp < 0) {
            if (!sol->viol_vars.empty() && (sol->total_viol.val() > 0 || _method == FlatZincSpace::SAT)) {
                _ostream << "%% total violation: " << sol->total_viol << std::endl;
            } else if (sol->optVarIsInt() && sol->optVar() >= 0) {
                _ostream << "%% objective: " << sol->iv[sol->optVar()] << std::endl;
            }
        }
        if (success && sol_comp < 0) {
            _allBestSolutions->emplace_back(std::dynamic_pointer_cast<Gecode::Space>(sol));
            if (_flatZincOptions.allSolutions() && (sol->viol_vars.empty() || sol->total_viol.val() == 0)) {
                sol->print(_ostream, _printer);
                _ostream << "----------" << std::endl;
            }
            if (sol->method() == FlatZincSpace::SAT && sol->total_viol.val() == 0) {
                _optimumFound->store(true);
            }
            if (asset_id < _assets.size()) {
                _finishedAsset = asset_id;
            }
        }
        _assets[asset_id]->incrSolutions(1);
    }
    _solutionMutex.unlock();

    return sol_comp < 0;
}

int SearchController::banditArmId(FlatZincSpace::AssetType assetType, bool useSelfSubsumingPropagators,
    bool useDependencyCuratedLns) const {
    const size_t index = static_cast<size_t>(assetType);
    if (index >= _banditArmIds.size()) {
        return -1;
    }
    return _banditArmIds[index][useSelfSubsumingPropagators ? 1 : 0][useDependencyCuratedLns ? 1 : 0];
}

void SearchController::awaitRunnersCompleted() {
    _executionDoneEvent.wait();
}

// Print the statistics of the search.
void SearchController::solutionStatistics(BaseAsset* asset, Support::Timer& t_total, unsigned int _finishedAsset) {
    // Space failed before assets was created and search started.
    StatusStatistics statusStatistics = asset->statusStatistics();
    const double t_solve = asset->solveTime();
    const double totalTime = (t_total.stop() / 1000.0);
    const double solveTime = (t_solve / 1000.0);
    const double initTime = totalTime - solveTime;
    if (_finishedAsset == -1) {
        _ostream << std::endl
            << "%%%mzn-stat: initTime=" << initTime
            << std::endl;
        _ostream << "%%%mzn-stat: solveTime=" << solveTime
            << std::endl;
        _ostream << "%%%mzn-stat: solutions=" << _allBestSolutions->size()
            << std::endl;
        _ostream << "%%%mzn-stat: finished asset="
            << asset->assetTypeStr() << std::endl;
        _ostream << "%%%mzn-stat: variables="
            << (_flatZincSpace->getintVarCount() + _flatZincSpace->getboolVarCount() + _flatZincSpace->getsetVarCount()) << std::endl
            << "%%%mzn-stat: propagators=" << 0 << std::endl
            << "%%%mzn-stat: propagations=" << statusStatistics.propagate << std::endl
            << "%%%mzn-stat: nodes=" << 0 << std::endl
            << "%%%mzn-stat: failures=" << 1 << std::endl
            << "%%%mzn-stat: restarts=" << 0 << std::endl
            << "%%%mzn-stat: peakDepth=" << 0 << std::endl
            << "%%%mzn-stat-end" << std::endl
            << std::endl;
        return;
    }

    // Search was not unsatisfiable: Print statistics.
    unsigned int numPropagators = asset->numPropagators();
    Gecode::Search::Statistics stat = asset->engine()->statistics();
    if (_flatZincOptions.fullStatistics()) {
        const FlatZincSpace& fzs = asset->flatZincSpace();
        _ostream << std::endl
            << "%%%mzn-stat: initTime=" << initTime
            << std::endl;
        _ostream << "%%%mzn-stat: solveTime=" << solveTime
            << std::endl;
        _ostream << "%%%mzn-stat: solutions=" << _allBestSolutions->size()
            << std::endl;
        _ostream << "%%%mzn-stat: finished asset="
            << asset->assetTypeStr() << std::endl;
        _ostream << "%%%mzn-stat: variables="
            << (fzs.getintVarCount() + fzs.getboolVarCount() + fzs.getsetVarCount()) << std::endl
            << "%%%mzn-stat: propagators=" << numPropagators << std::endl
            << "%%%mzn-stat: propagations=" << statusStatistics.propagate+stat.propagate << std::endl
            << "%%%mzn-stat: nodes=" << stat.node << std::endl
            << "%%%mzn-stat: failures=" << stat.fail << std::endl
            << "%%%mzn-stat: restarts=" << stat.restart << std::endl
            << "%%%mzn-stat: peakDepth=" << stat.depth << std::endl
            << "%%%mzn-stat-end" << std::endl
            << std::endl;

        for (long unsigned int a = 0; a < _assets.size(); a++) {
            if (static_cast<int>(a) == _finishedAsset) {
                continue;
            }
            numPropagators = _assets[a]->numPropagators();
            if (_assets[a]->assetType() == FlatZincSpace::AssetType::SHAVING) {
                _ostream << "%%%mzn-stat: unfinished asset="
                    << _assets[a]->assetTypeStr() << std::endl;
                _ostream << "%%%mzn-stat: propagators=" << numPropagators << std::endl
                    << "%%%mzn-stat: propagations=" << statusStatistics.propagate+stat.propagate << std::endl
                    << "%%%mzn-stat: foundFailures=" << _forbiddenLiterals.size() << std::endl
                    << "%%%mzn-stat-end" << std::endl
                    << std::endl;
                continue;
            }
            stat = _assets[a]->engine()->statistics();
            numPropagators = _assets[a]->numPropagators();
            _ostream << "%%%mzn-stat: unfinished asset="
                << _assets[a]->assetTypeStr() << std::endl;
            _ostream << "%%%mzn-stat: solutions=" << _assets[a]->numSolutions() << std::endl
                << "%%%mzn-stat: propagators=" << numPropagators << std::endl
                << "%%%mzn-stat: propagations=" << statusStatistics.propagate+stat.propagate << std::endl
                << "%%%mzn-stat: nodes=" << stat.node << std::endl
                << "%%%mzn-stat: failures=" << stat.fail << std::endl
                << "%%%mzn-stat: restarts=" << stat.restart << std::endl
                << "%%%mzn-stat: peakDepth=" << stat.depth << std::endl
                << "%%%mzn-stat-end" << std::endl
                << std::endl;
        }
    }
    else{
        _ostream << std::endl
            << "%%%mzn-stat: initTime=" << initTime
            << std::endl;
        _ostream << "%%%mzn-stat: solveTime=" << solveTime
            << std::endl;
        _ostream << "%%%mzn-stat: solutions=" << _allBestSolutions->size()
            << std::endl;
        _ostream << "%%%mzn-stat: finished asset="
            << asset->assetTypeStr() << std::endl;
        _ostream << "%%%mzn-stat: variables="
            << (_flatZincSpace->getintVarCount() + _flatZincSpace->getboolVarCount() + _flatZincSpace->getsetVarCount()) << std::endl
            << "%%%mzn-stat: propagators=" << numPropagators << std::endl
            << "%%%mzn-stat: propagations=" << statusStatistics.propagate+stat.propagate << std::endl
            << "%%%mzn-stat: nodes=" << stat.node << std::endl
            << "%%%mzn-stat: failures=" << stat.fail << std::endl
            << "%%%mzn-stat: restarts=" << stat.restart << std::endl
            << "%%%mzn-stat: peakDepth=" << stat.depth << std::endl
            << "%%%mzn-stat-end" << std::endl
            << std::endl;
    }
}

void SearchController::createBanditArmAsset(unsigned int assetId) {
    _assets[assetId] = (std::make_unique<BanditArmAsset>(*this, *_flatZincSpace, _flatZincOptions, assetId));
    _assets[assetId]->setAssetTypeStr("bandit arm asset");
}

void SearchController::createAsset(FlatZincSpace::AssetType asset, unsigned int assetId, bool useSelfSubsumingPropagators) {
    switch (asset)
    {
    case FlatZincSpace::AssetType::SHAVING:
        _assets[assetId] = (std::make_unique<ShavingAsset>(*this, *_flatZincSpace, _flatZincOptions, assetId, asset, 20, true, new LargestAFCVariableSorter()));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("shaving asset");
        }
        break;
    case FlatZincSpace::AssetType::USER:
        _assets[assetId] = (std::make_unique<DFSAsset>(*this, *_flatZincSpace, _flatZincOptions, assetId, asset, 1, useSelfSubsumingPropagators));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("bab asset");
        }
        break;
    case FlatZincSpace::AssetType::PB_USER:
        _assets[assetId] = (std::make_unique<DFSAsset>(*this, *_flatZincSpace, _flatZincOptions, assetId, asset, 1, useSelfSubsumingPropagators));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("prioritized branching bab asset");
        }
        break;
    case FlatZincSpace::AssetType::USER_OPPOSITE:
        _assets[assetId] = (std::make_unique<DFSAsset>(*this, *_flatZincSpace, _flatZincOptions, assetId, asset, 1, useSelfSubsumingPropagators));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("bab opposite branching asset");
        }
        break;
    default:
        break;
    }
}

bool isLnsType(FlatZincSpace::AssetType assetType) {
    switch (assetType) {
        case FlatZincSpace::AssetType::LNS_USER:
        case FlatZincSpace::AssetType::PGLNS:
        case FlatZincSpace::AssetType::CIGLNS:
        case FlatZincSpace::AssetType::OBJRELLNS:
        case FlatZincSpace::AssetType::SVRLNS:
        case FlatZincSpace::AssetType::REVPGLNS:
            return true;
        default:
            return false;
    }
}

bool SearchController::isValidBanditArm(bool hasSatisfyingSolution, FlatZincSpace::AssetType assetType, bool useSelfSubsumingPropagators, bool useDependencyCuratedLns) const {
    if (!isLnsType(assetType)) {
        // DFS/BAB cannot be used with dependency curation
        return !useDependencyCuratedLns;
    }
    bool ret = true;
    if (useSelfSubsumingPropagators) {
        if (hasSatisfyingSolution) {
            return false;
        }
    } else {
        // For LNS without self-subsuming propagators to work,
        // the problem must be a COP and there must be an incumbent solution
        ret &= _method != FlatZincSpace::SAT && !_allBestSolutions->empty();
    }
    if (assetType == FlatZincSpace::AssetType::CIGLNS) {
        ret &= _flatZincSpace->_objective_is_sum;
    }
    return ret;
}

void SearchController::updateMultiArmedBandit() {
    std::vector<FlatZincSpace::AssetType> validBanditAssetTypes;
    // Select the assets to use depending on method, number of solutions required and number of threads available.
    // The order of the assets in the vector is the order of priority (Given from the results of the thesis).
    // It also makes sense not to use LNS as the first assets to be created, as they need a solution to function properly (even though the time difference is extremely small).
    if (0 <= _flatZincOptions.pbsAssetType() && _flatZincOptions.pbsAssetType() <= 9) {
        validBanditAssetTypes = {static_cast<FlatZincSpace::AssetType>(_flatZincOptions.pbsAssetType())};
    } else {
        // If optimization problem, then use all available search assets.
        validBanditAssetTypes = {
            FlatZincSpace::AssetType::CIGLNS,
            FlatZincSpace::AssetType::OBJRELLNS,
            FlatZincSpace::AssetType::SVRLNS,
            FlatZincSpace::AssetType::PGLNS,
            FlatZincSpace::AssetType::REVPGLNS,
            FlatZincSpace::AssetType::LNS_USER};
    }

    bool hasSatisfyingSol = false;
    if (_flatZincSpace->_incumbentSolution->hasValue()) {
        auto sol = _flatZincSpace->_incumbentSolution->load();
        hasSatisfyingSol = sol->viol_vars.empty() || sol->total_viol.val() == 0;
    }

    _banditMutex.lock();
    ++_banditTimestamp;
    auto assets = std::vector<size_t>{
        static_cast<size_t>(FlatZincSpace::AssetType::USER),
        static_cast<size_t>(FlatZincSpace::AssetType::LNS_USER),
        static_cast<size_t>(FlatZincSpace::AssetType::PGLNS),
        static_cast<size_t>(FlatZincSpace::AssetType::CIGLNS),
        static_cast<size_t>(FlatZincSpace::AssetType::OBJRELLNS),
        static_cast<size_t>(FlatZincSpace::AssetType::SVRLNS),
        static_cast<size_t>(FlatZincSpace::AssetType::REVPGLNS),
        static_cast<size_t>(FlatZincSpace::AssetType::PB_USER),
        static_cast<size_t>(FlatZincSpace::AssetType::USER_OPPOSITE),
        static_cast<size_t>(FlatZincSpace::AssetType::SHAVING),
        static_cast<size_t>(FlatZincSpace::AssetType::DUMMY)};
    const size_t maxAssetType = *std::max_element(assets.begin(), assets.end());
    _banditArmIds.resize(maxAssetType + 1, std::array<std::array<int, 2>, 2>{std::array<int, 2>{-1, -1}});
    _armIdToAssetType.clear();
    _armIdToSelfSubsuming.clear();
    _armIdToCuratedDependency.clear();

    int numArms = 0;
    for (int i = static_cast<int>(validBanditAssetTypes.size()) - 1; i >= 0; --i) {
        for (bool useSelfSubsumingPropagators : std::array{false, true}) {
            for (bool useDependencyCuratedLns : std::array{false, true}) {
                if (isValidBanditArm(hasSatisfyingSol, validBanditAssetTypes[i], useSelfSubsumingPropagators, useDependencyCuratedLns)) {
                    _banditArmIds.at(static_cast<size_t>(validBanditAssetTypes[i])).at(useSelfSubsumingPropagators ? 1 : 0).at(useDependencyCuratedLns ? 1 : 0) = numArms;
                    _armIdToAssetType.emplace_back(validBanditAssetTypes[i]);
                    _armIdToSelfSubsuming.emplace_back(useSelfSubsumingPropagators);
                    _armIdToCuratedDependency.emplace_back(useDependencyCuratedLns);
                    ++numArms;
                }
            }
        }
    }
    _bandit = std::make_unique<Bandit>(numArms);
    _banditMutex.unlock();
}

void SearchController::createAssets(double initTime) {
    // Vector of asset type and the number of threads to use for that asset type.
    std::array<std::pair<FlatZincSpace::AssetType, bool>, 2> defaultCompleteTypes{
                std::pair<FlatZincSpace::AssetType, bool>{FlatZincSpace::AssetType::USER, false},
                std::pair<FlatZincSpace::AssetType, bool>{FlatZincSpace::AssetType::USER, true}};

    const int numCompleteAssets = defaultCompleteTypes.size();
    const int numLnsAssets = static_cast<int>(_flatZincOptions.threads()) - numCompleteAssets;
    const bool useShaving = false && _flatZincOptions.threads() - numCompleteAssets - numLnsAssets > 0;

    // Set array sizes indexed by the assets id.
    _assets.resize(_flatZincOptions.threads());
    _assetSwappedEngine.resize(_flatZincOptions.threads(), false);
    _runningThreads = _flatZincOptions.threads();

    updateMultiArmedBandit();

    // Create complete assets:
    int assetId = 0;
    for (const auto [completeAsset, useNonFailingPropagators] : defaultCompleteTypes) {
        createAsset(completeAsset, assetId, useNonFailingPropagators);
        ++assetId;
    }
    for (int i = 0; i < numLnsAssets; ++i) {
        createBanditArmAsset(assetId);
        ++assetId;
    }
    if (useShaving) {
        createAsset(FlatZincSpace::AssetType::SHAVING, assetId, false);
        ++assetId;
    }
    for (auto& asset : _assets) {
        asset->increaseSolveTime(initTime);
        asset->setStatusStatistics(_statusStatistics);
    }
}

// The controller that creates the workers and controls the searches.
bool SearchController::init() {
    Support::Timer propTimer;
    propTimer.start();
    _flatZincSpace->populateCombinedObjective(_flatZincOptions);
    const SpaceStatus preSearchProp = _flatZincSpace->status(_statusStatistics);
    const double initTime = propTimer.stop();
    // Make search space clone-able by calling status on it. If it fails, then the model is unsatisfiable.
    // If the space is unsatisfiable before the search even starts, then finish and print statistics through dummy asset.
    if (preSearchProp == SS_FAILED) {
        _ostream << "=====UNSATISFIABLE=====" << std::endl;
        // Create dummy asset so that information about UNSAT space can be printed out:
        if (_assets.empty()) {
            _assets.emplace_back(std::make_unique<BaseAsset>(*_flatZincSpace, _flatZincOptions));
        } else {
            _assets[0] = std::make_unique<BaseAsset>(*_flatZincSpace, _flatZincOptions);
        }
        _assets[0]->setStatusStatistics(_statusStatistics);
        _assets[0]->increaseSolveTime(initTime);
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[0]->setAssetTypeStr("none");
            solutionStatistics(_assets[0].get(), _timerTotal, -1);
        }
        return false;
    }

    // Populate the initial solution
    if (FlatZincSpace::hasInitialIncumbentSolution(_flatZincSpace->solveAnnotations())) {
        auto* clone = _flatZincSpace->deepClone();
        rel(*clone, clone->total_viol, IRT_EQ, 0);
        auto bm = BranchModifier(false, false, false);
        clone->applyInitialIncumbentSolution(_flatZincSpace->solveAnnotations());
        const auto sol = std::shared_ptr<FlatZincSpace>(dynamic_cast<FlatZincSpace*>(clone->clone()));
        delete clone;
        updateBestSolution(sol, std::numeric_limits<unsigned int>::max());
    }

    // setup and create the assets.
    createAssets(initTime);
    return true;
}

// The controller that creates the workers and controls the searches.
void SearchController::run() {
    // run the assets.
    for (auto &asset : _assets) {
        asset->run();
    }
    awaitRunnersCompleted();
    
    // If the shaving asset finished, the problem is unsatisfiable.
    if (_finishedAsset < _assets.size() && _assets[_finishedAsset]->assetType() == FlatZincSpace::AssetType::SHAVING) {
        _ostream << "=====UNSATISFIABLE=====" << std::endl;
    } else {
        // Print the best or final solution:
        const auto sol = _flatZincSpace->_incumbentSolution->load();
        // Not a guarantee that a solution is found and finished asset it set.
        // Use default user asset in case no solution was found.
        BaseEngine* se = _assets[_finishedAsset > _assets.size() ? 0 : _finishedAsset]->engine();

        bool hasViolations = sol == nullptr ? true : sol->total_viol.val() > 0;

        if (!hasViolations) {
            sol->print(_ostream, _printer);
            _ostream << "----------" << std::endl;
        }
        if (se && !se->stopped()) {
            if (sol) {
                _ostream << "==========" << std::endl;
            } else {
                _ostream << "=====UNSATISFIABLE=====" << std::endl;
            }
        }
        else if (hasViolations) {
            _ostream << "=====UNKNOWN=====" << std::endl;
        }
    }
    // If print Statistics:
    if (_finishedAsset < _assets.size() && _flatZincOptions.mode() == SM_STAT) {
        solutionStatistics(_assets[_finishedAsset].get(), _timerTotal, _finishedAsset);
    }

    // Delete allocated arrays in fzs.
    _flatZincSpace->deletePBSArrays();
}
// ########################################################################
//                         Multi Armed Bandit below.
// ########################################################################
Bandit::Bandit(const size_t numArms, const double temperature, const double learningRate) :
    _numArms(numArms),
    _temperature(temperature),
    _totalReward(numArms, 0.0),
    _averageReward(numArms, 0.0),
    _armTotalCount(numArms, 0) {}

size_t Bandit::randomArm(std::vector<double>& weights) {
    std::random_device rd;
    std::mt19937_64 generator(rd());
    auto distro = std::discrete_distribution<size_t>(weights.begin(), weights.end());
    return distro(generator);
}


size_t Bandit::randomArm() const {
    std::random_device rd;
    std::mt19937_64 generator(rd());

    std::uniform_real_distribution<double> epsilon_distro(0, 1);
    const double rand_num = epsilon_distro(generator);

    if (rand_num < _temperature) {
        //random action
        std::uniform_int_distribution<size_t> action_distro(0, _numArms - 1);
        return action_distro(generator);
    }
    //greedy action
    return std::distance(_averageReward.begin(), std::max_element(_averageReward.begin(), _averageReward.end()));
}

size_t Bandit::softMax(const double tau) const {

    std::vector<double> weights(_numArms);
    for (size_t i = 0; i < _numArms; i++) {
        weights[i] = exp(_averageReward[i] / tau);
    }

    double denominator = 0;
    for (size_t i = 0; i < _numArms; i++) {
        denominator += weights[i];
    }
    for (size_t i = 0; i < _numArms; i++) {
        weights[i] /= denominator;
    }

    return randomArm(weights);

}

void Bandit::updateReward(const size_t arm, const double reward) {
    assert(arm < _numArms);
    ++_totalCount;
    ++_armTotalCount[arm];
    _totalReward[arm] += reward;
    _averageReward[arm] += _totalReward[arm] / static_cast<double>(_armTotalCount[arm]);
}

void Bandit::updateRewardUCB(const size_t arm, const double reward, const double beta) {
    assert(arm < _numArms);
    ++_totalCount;
    ++_armTotalCount[arm];
    _ucb = sqrt(2 * beta * log(static_cast<double>(_armTotalCount[arm]) / static_cast<double>(_armTotalCount[arm])));
    const double ucbReward = reward + _ucb;
    _totalReward[arm] += ucbReward;
    _averageReward[arm] = _totalReward[arm]/static_cast<double>(_armTotalCount[arm]);
}


size_t Bandit::bestArm() const {
    return std::distance(_averageReward.begin(), std::max_element(_averageReward.begin(), _averageReward.end()));
}

// ########################################################################
//                         AssetExecutor below.
// ########################################################################
void AssetExecutor::runSearch() {

    StatusStatistics statusStatistics = asset->statusStatistics();
    // Start the search timer.
    Support::Timer t_solve;
    t_solve.start();
    if (asset->flatZincSpace().status(statusStatistics) == SS_FAILED) {
        control.thread_done();
        return;
    }
    asset->setNumPropagators(PropagatorGroup::all.size(asset->flatZincSpace()));
    asset->setStatusStatistics(statusStatistics);

    size_t round = 0;

    do {
        asset->updateBanditArmId();
        // update engine with new timeout
        if (round > 0) {
            asset->updateEngine();
        }
        BaseEngine* engine = asset->engine();

        // Run the search engine.
        assert(engine != nullptr);
        std::shared_ptr<FlatZincSpace> sol;
        bool solWasBestSol = false;

        while (auto nextSol = std::shared_ptr<FlatZincSpace>(engine->next())) {
            if (control._optimumFound->load()) {
                break;
            }
            // If last solution was not the current best solution, delete it.
            if (!solWasBestSol && sol != nullptr) {
                sol = nullptr;
            }
            sol = nextSol;

            solWasBestSol = control.updateBestSolution(sol, asset_id);
            if (solWasBestSol && sol->method() == FlatZincSpace::SAT && sol->total_viol.val() == 0) {
                break;
            }

            // Apply nq constraints to make asset take advantage of shaving.
            std::vector<Literal> local_forbidden_literals = control.get_forbidden_literals();
            const size_t size = local_forbidden_literals.size();
            if (size > asset->shavingStart()) {
                for (size_t i = asset->shavingStart(); i < size; i++) {
                    local_forbidden_literals[i].var.nq(&(asset->flatZincSpace()), local_forbidden_literals[i].value);
                }
            }

            // Change the search engine to update cd and ad.
            auto stats = engine->statistics();
            if (asset->assetType() != FlatZincSpace::AssetType::USER && !control._assetSwappedEngine[asset_id] && stats.depth > 50) {
                Search::Options& searchOptions = asset->searchOptions();
                searchOptions.c_d *= stats.depth;
                searchOptions.a_d *= 2;

                delete engine;
                if (asset->assetType() != FlatZincSpace::AssetType::DUMMY) {
                    fopt.restart(RM_LUBY);
                    fopt.restart_base(1.5);
                    fopt.restart_scale(250);
                    assert(searchOptions.cutoff != nullptr);
                    // delete searchOptions.cutoff;
                    searchOptions.cutoff = new Search::CutoffAppend(new Search::CutoffConstant(0), 1, Driver::createCutoff(fopt));
                    auto* e = dynamic_cast<RBSEngine*>(engine);
                    auto* upd_se = new RBSEngine(asset->curFlatZincSpace(), searchOptions, control._optimumFound, control._allBestSolutions);
                    asset->setEngine(dynamic_cast<BaseEngine*>(upd_se));
                    engine = upd_se;
                } else {
                    if (control._method == FlatZincSpace::SAT)
                    {
                        auto* upd_se = new DFSEngine(asset->curFlatZincSpace(), searchOptions);
                        asset->setEngine(dynamic_cast<BaseEngine*>(upd_se));
                        engine = upd_se;
                    }
                    else
                    {
                        auto* upd_se = new BABEngine(asset->curFlatZincSpace(), searchOptions);
                        asset->setEngine(dynamic_cast<BaseEngine*>(upd_se));
                        engine = upd_se;
                    }
                }
                control._assetSwappedEngine[asset_id] = true;
            }
        }
        ++round;
    } while (asset->runNextRound());
    // Stop the search timer.
    const double t = t_solve.stop();
    if (!asset->engine()->stopped() && !isLnsType(asset->assetType())) {
        control._optimumFound->store(true);
    }
    asset->increaseSolveTime(t);
    control.thread_done();
}

// Go through and run each asset in the round-robin for some fixed amount of restarts. Store the number of sols for each asset, best asset keeps on running until search finishes.
void RoundRobinLNSAsset::run() {
    bool curBestViol = std::numeric_limits<int>::max();
    int curBestObj = control._method == FlatZincSpace::MAX ? std::numeric_limits<int>::min() : std::numeric_limits<int>::max();

    const int optVar = _roundRobinAssets[0]->flatZincSpace().optVar();
    Support::Timer t_solve;

    for (long unsigned int i = 0; i < _roundRobinAssets.size(); i++) {
        // Do one run of the asset and decide which asset is the best.
        BaseEngine *se = _roundRobinAssets[i]->engine();
        t_solve.start();
        auto sol = std::shared_ptr<FlatZincSpace>(se->next());
        _roundRobinAssets[i]->increaseSolveTime(t_solve.stop());

        control.updateBestSolution(sol, _assetId);

        const int curViol = sol->viol_vars.empty() ? 0 : sol->total_viol.val();
        const int curObj = sol->iv[optVar].val();
        const bool isBetterSolution =
            curViol < curBestViol ||
            (curViol == curBestViol && control._method != FlatZincSpace::SAT &&
            (control._method == FlatZincSpace::MAX ? curObj > curBestObj : curObj < curBestObj));
        if (isBetterSolution) {
            curBestViol = curViol;
            curBestObj = curObj;
            best_asset = std::move(_roundRobinAssets[i]);
        }

        if (_flatZincOptions.mode() == SM_STAT) {
            switch (best_asset->assetType())
            {
                case FlatZincSpace::AssetType::LNS_USER:
                    best_asset->setAssetTypeStr("round robin asset random lns");
                    break;
                case FlatZincSpace::AssetType::PGLNS:
                    best_asset->setAssetTypeStr("round robin asset propagation guided lns");
                    break;
                case FlatZincSpace::AssetType::REVPGLNS:
                    best_asset->setAssetTypeStr("round robin asset reversed propagation guided lns");
                    break;
                case FlatZincSpace::AssetType::OBJRELLNS:
                    best_asset->setAssetTypeStr("round robin asset objective relaxation lns");
                    break;
                case FlatZincSpace::AssetType::CIGLNS:
                    best_asset->setAssetTypeStr("rounds robin asset cost impact guided lns");
                    break;
                case FlatZincSpace::AssetType::SVRLNS:
                    best_asset->setAssetTypeStr("round robin asset static variable relationship lns");
                    break;
                case FlatZincSpace::AssetType::DUMMY:
                    best_asset->setAssetTypeStr("round robin asset");
                    break;
            }
        }

        // If search is finished (solution has been found, then return (since we are done))
        if (control._optimumFound->load()) {
            // Select any asset as solution has already been found.
            best_asset = std::move(_roundRobinAssets[i]);
            control.thread_done();
            return;
        }
    }
    // Unless search has finished, use the best engine and perform actual search:
    if (!control._optimumFound->load()) {
        // If no solution was found.
        if (best_asset != nullptr) {
            double prev_solveTime = best_asset->solveTime();
            best_asset->increaseSolveTime(prev_solveTime);
            best_asset->run();
        } else {
            best_asset = std::move(_roundRobinAssets[0]);
            control.thread_done();
        }
    }
}

void AssetExecutor::runShaving() {
    // Cast asset to be a ShavingAsset.
    auto* shaving_asset = dynamic_cast<ShavingAsset*>(asset);

    StatusStatistics status_stat;
    const CloneStatistics clone_stat;

    bool has_reported_literal = false;
    

    
    Support::Timer t_solve;
    t_solve.start();
    if (asset->flatZincSpace().status(status_stat) != SS_FAILED) {
        asset->setNumPropagators(PropagatorGroup::all.size(asset->flatZincSpace()));
        asset->setStatusStatistics(status_stat);
    }

    // Shave bounds
    if (shaving_asset->doBoundsShaving()) {
        shaving_asset->runShavingPass(control, status_stat, clone_stat, has_reported_literal, [](VarDescription& vd, FlatZincSpace* s) {
            return vd.bounds_literals(s);
        });
    }
    else {
        shaving_asset->runShavingPass(control, status_stat, clone_stat, has_reported_literal, [shaving_asset](VarDescription& vd, FlatZincSpace* s) {
            if (vd.size(s) > static_cast<unsigned int>(shaving_asset->getMaxDomShavingSize())) {
                return std::vector<Literal>{};
            }
            return vd.domain_literals(s);
        });
    }
    
    asset->increaseSolveTime(t_solve.stop());
    asset->setStatusStatistics(status_stat);

    control.thread_done();
}

// ########################################################################
//                         Assets Below.
// ########################################################################

BaseAsset::BaseAsset(FlatZincSpace &flatZincSpace, FlatZincSpace *curFlatZincSpace, FlatZincOptions &flatZincOptions,
    unsigned int assetId, FlatZincSpace::AssetType assetType, bool useSelfSubsumingPropagators,
    bool useDependencyCuratedLns):
_originalFlatZincSpace(flatZincSpace),
_curFlatZincSpace(curFlatZincSpace),
_flatZincOptions(flatZincOptions),
_assetType(assetType),
_assetId(assetId),
_useSelfSubsumingPropagators(useSelfSubsumingPropagators),
_useDependencyCuratedLns(useDependencyCuratedLns) {
    if (_curFlatZincSpace != nullptr) {
        _curFlatZincSpace->setAssetType(_assetType);
        _curFlatZincSpace->use_dependency_curated_lns = useDependencyCuratedLns;
        _curFlatZincSpace->_use_soft_subsume = useSelfSubsumingPropagators;
        _curFlatZincSpace->populateLnsVars(_originalFlatZincSpace.constraints);
        _curFlatZincSpace->storeConstraintInformation(_originalFlatZincSpace.constraints);
    }
}

std::shared_ptr<Search::Options> BaseAsset::generateSearchOptions(FlatZincSpace& originalFlatZincSpace, Search::Stop* stop) const {
    auto searchOptions = std::make_shared<Search::Options>();
    searchOptions->stop = stop;
    searchOptions->c_d = _flatZincOptions.c_d();
    searchOptions->a_d = _flatZincOptions.a_d();

#ifdef GECODE_HAS_FLOAT_VARS
    originalFlatZincSpace.step = _flatZincOptions.step();
#endif

    searchOptions->numThreads = numThreads();
    searchOptions->nogoods_limit = _flatZincOptions.nogoods() ? _flatZincOptions.nogoods_limit() : 0;

    if (_flatZincOptions.restart() != RM_NONE) {
        _flatZincOptions.restart(RM_NONE);
    }

    auto* fznCutoff = Driver::createCutoff(_flatZincOptions);
    assert(searchOptions->cutoff == nullptr);
    if (fznCutoff == nullptr) {
        searchOptions->cutoff = new Search::CutoffConstant(0);
    } else {
        searchOptions->cutoff = new Search::CutoffAppend(new Search::CutoffConstant(0), 1, fznCutoff);
    }
    if (_flatZincOptions.interrupt()) {
        Driver::PBSCombinedStop::installCtrlHandler(true);
    }
    return searchOptions;
}

bool BaseAsset::oppositeBranching() const {
    return _assetType == FlatZincSpace::AssetType::USER_OPPOSITE;
}

bool BaseAsset::pbsBranching() const {
    return _assetType == FlatZincSpace::AssetType::CIGLNS;
}

bool BaseAsset::sortFlatAnnotations() const {
    return _assetType == FlatZincSpace::AssetType::PB_USER;
}

bool BaseAsset::runNextRound() const {
    return false;
}

DFSAsset::DFSAsset(SearchController &searchController, FlatZincSpace& fg, FlatZincOptions &fopt,
                   unsigned int assetId, FlatZincSpace::AssetType assetType, unsigned int numThreads, bool useSelfSubsumingPropagators) :
BaseAsset(fg, fg.deepClone(), fopt, assetId, assetType, useSelfSubsumingPropagators),
_numThreads(numThreads),
_searchController(searchController),
_branchModifier(oppositeBranching(), pbsBranching(), sortFlatAnnotations()),
executor(new AssetExecutor(searchController, this, fopt, assetId, true)) {
    _curFlatZincSpace->postConstraints(_originalFlatZincSpace.constraints, 7 <= _assetId && _assetId <= 8);
    if (_assetId == 7) {
        _branchModifier.use_pbs_branching = !_originalFlatZincSpace.solveAnnotations();
        if (_branchModifier.use_pbs_branching) {
            _branchModifier.PBAssetBranching(_originalFlatZincSpace.constraints);
        }
    }

    _curFlatZincSpace->createBranchers(searchController._printer, _originalFlatZincSpace.solveAnnotations(), _flatZincOptions, false, _branchModifier, std::cerr);

    assert(_searchOptions == nullptr);
    _searchOptions = std::make_shared<Search::Options>();
    _searchOptions->c_d = _searchOptions->c_d;
    _searchOptions->a_d = _searchOptions->a_d;
    _searchOptions->numThreads = _numThreads;
    _searchOptions->stop = Driver::PBSCombinedStop::create(
        0,
        0,
        _flatZincOptions.time(),
        0,
        true,
        _searchController._optimumFound);

    if (_flatZincOptions.interrupt()) {
        Driver::PBSCombinedStop::installCtrlHandler(true);
    }

    if (searchController._method == FlatZincSpace::SAT)
    {
        _engine = new DFSEngine(_curFlatZincSpace, *_searchOptions);
    }
    else
    {
        _engine = new BABEngine(_curFlatZincSpace, *_searchOptions);
    }
}

LNSAsset::LNSAsset(SearchController &searchController, FlatZincSpace& fg, FlatZincOptions &fopt,
    unsigned int assetId, FlatZincSpace::AssetType assetType, bool useSelfSubsumingPropagators,
    bool useDependencyCuratedLns, RestartMode restartMode, double restartBase, unsigned int restartScale)
: BaseAsset(fg, fg.deepClone(), fopt, assetId, assetType, searchController._allBestSolutions->empty() || useSelfSubsumingPropagators,
    useDependencyCuratedLns),
_searchController(searchController),
_branchModifier(oppositeBranching(), pbsBranching(), sortFlatAnnotations()),
_restartMode(restartMode),
_restartBase(restartBase),
_restartScale(restartScale),
executor(new AssetExecutor(searchController, this, fopt, assetId, true)) {

    if (_flatZincOptions.interrupt()) {
        Driver::PBSCombinedStop::installCtrlHandler(true);
    }

    // Setup branching strategies for the asset before creating the branchers.
    _curFlatZincSpace->postConstraints(_originalFlatZincSpace.constraints, _assetId <= 6);

    // If not RBS but asset is to use it:
    if (_flatZincOptions.restart() == RM_NONE) {
        _flatZincOptions.restart(_restartMode);
        _flatZincOptions.restart_base(_restartBase);
        _flatZincOptions.restart_scale(_restartScale);
    }

    assert(_searchOptions == nullptr);
    _searchOptions = generateSearchOptions(
        _originalFlatZincSpace,
        Driver::PBSCombinedStop::create(
            _flatZincOptions.node(),
            _flatZincOptions.fail(),
            _flatZincOptions.time(),
            _flatZincOptions.restart_limit(),
            true,
            searchController._optimumFound));

    _curFlatZincSpace->createBranchers(searchController._printer, _originalFlatZincSpace.solveAnnotations(), _flatZincOptions, false, _branchModifier, std::cerr);

    _engine = new RBSEngine(_curFlatZincSpace, *_searchOptions, searchController._optimumFound, searchController._allBestSolutions);
}

BanditArmAsset::BanditArmAsset(SearchController &searchController, FlatZincSpace& fg, FlatZincOptions &fopt,
    unsigned int assetId, RestartMode restartMode, double restartBase, unsigned int restartScale)
: BaseAsset(fg, fg.deepClone(), fopt, assetId, FlatZincSpace::AssetType::LNS_USER, searchController._allBestSolutions->empty(), false),
_searchController(searchController),
_branchModifier(oppositeBranching(), pbsBranching(), sortFlatAnnotations()),
_restartMode(restartMode),
_restartBase(restartBase),
_restartScale(restartScale),
executor(new AssetExecutor(searchController, this, fopt, assetId, true)) {
    _timeout.start();

    if (_flatZincOptions.interrupt()) {
        Driver::PBSCombinedStop::installCtrlHandler(true);
    }

    // Setup branching strategies for the asset before creating the branchers.
    _curFlatZincSpace->postConstraints(_originalFlatZincSpace.constraints, _assetId <= 6);

    // If not RBS but asset is to use it:
    if (_flatZincOptions.restart() == RM_NONE) {
        _flatZincOptions.restart(_restartMode);
        _flatZincOptions.restart_base(_restartBase);
        _flatZincOptions.restart_scale(_restartScale);
    }

    const double timeout = std::min(defaultTime,  _flatZincOptions.time() - _timeout.stop());
    assert(_searchOptions == nullptr);
    _searchOptions = generateSearchOptions(
        _originalFlatZincSpace,
        Driver::PBSCombinedStop::create(
            _flatZincOptions.node(),
            _flatZincOptions.fail(),
            timeout,
            _flatZincOptions.restart_limit(),
            true,
            _searchController._optimumFound));

    _curFlatZincSpace->createBranchers(_searchController._printer, _originalFlatZincSpace.solveAnnotations(), _flatZincOptions, false, _branchModifier, std::cerr);

    _engine = new RBSEngine(_curFlatZincSpace, *_searchOptions, _searchController._optimumFound, _searchController._allBestSolutions);
}

void BanditArmAsset::updateBanditArmId() {
    if (_banditArmId < 0) {
        return;
    }
    // lock
    _searchController._banditMutex.lock();

    // update reward if bandit has not changed.
    if (_searchController.banditTimestamp() == _banditTimestamp) {
        _searchController._bandit->updateReward(_banditArmId, static_cast<double>(_numCurSolutions));
    }
    // get new arm
    _banditArmId = _searchController._bandit->softMax();
    // update local parameters
    _assetType = _searchController.assetType(_banditArmId, false);
    _useSelfSubsumingPropagators = _searchController.useSelfSubsumingPropagators(_banditArmId, false);
    _useDependencyCuratedLns = _searchController.useDependencyCuratedLns(_banditArmId, false);
    _banditTimestamp = _searchController.banditTimestamp();
    // unlock
    _searchController._banditMutex.unlock();

    _numCurSolutions = 0;

    // Update current FlatZincSpace
    _curFlatZincSpace->setAssetType(_assetType);
    _curFlatZincSpace->use_dependency_curated_lns = _useDependencyCuratedLns;
    _curFlatZincSpace->_use_soft_subsume = _useSelfSubsumingPropagators;
    _curFlatZincSpace->populateLnsVars(_originalFlatZincSpace.constraints);
    _curFlatZincSpace->storeConstraintInformation(_originalFlatZincSpace.constraints);
}

bool BanditArmAsset::runNextRound() const {
    return !_searchController._optimumFound->load() && _timeout.stop() < _flatZincOptions.time();
}

void BanditArmAsset::updateEngine() {
    delete _engine;
    assert(_searchOptions != nullptr);
    delete _searchOptions->stop;

    // refresh the stop
    const double timeout = std::min(defaultTime,  _flatZincOptions.time() - _timeout.stop());
    _searchOptions->stop = Driver::PBSCombinedStop::create(
        _flatZincOptions.node(),
        _flatZincOptions.fail(),
        timeout,
        _flatZincOptions.restart_limit(),
        true,
        _searchController._optimumFound);

    auto* fznCutoff = Driver::createCutoff(_flatZincOptions);
    if (fznCutoff == nullptr) {
        _searchOptions->cutoff = new Search::CutoffConstant(0);
    } else {
        _searchOptions->cutoff = new Search::CutoffAppend(new Search::CutoffConstant(0), 1, fznCutoff);
    }
    _engine = new RBSEngine(_curFlatZincSpace, *_searchOptions);
}

RoundRobinLNSAsset::RoundRobinLNSAsset(SearchController &control, FlatZincSpace& fg, FlatZincOptions &fopt,
                                       unsigned int asset_id) :
BaseAsset(fg, nullptr, fopt, asset_id, FlatZincSpace::AssetType::DUMMY),
best_asset(nullptr), control(control) {
    // Fill the round_robin_assets vector with all types of LNS assets available.
    // Ordering of assets can help (Now following thesis results).
    const auto assets = std::vector<FlatZincSpace::AssetType>{
        {FlatZincSpace::AssetType::CIGLNS},
        {FlatZincSpace::AssetType::OBJRELLNS},
        {FlatZincSpace::AssetType::SVRLNS},
        {FlatZincSpace::AssetType::LNS_USER},
        {FlatZincSpace::AssetType::PGLNS},
        {FlatZincSpace::AssetType::REVPGLNS}};
    for (const auto assetType : assets) {
        _roundRobinAssets.emplace_back(std::make_unique<LNSAsset>(control, _originalFlatZincSpace, _flatZincOptions,
            asset_id, assetType));
    }
}

ShavingAsset::ShavingAsset(SearchController &control, FlatZincSpace& fg, FlatZincOptions &fopt,
    unsigned int assetId, FlatZincSpace::AssetType assetType, int maxDomShavingSize,
    bool do_bounds_shaving, VariableSorter *sorter): BaseAsset(fg, fg.deepClone(), fopt, assetId, assetType, 0),
                                                     control(control),
                                                     _executor(new AssetExecutor(control, this, fopt, assetId, false)),
                                                     _maxDomShavingSize(maxDomShavingSize),
                                                     _doBoundsShaving(do_bounds_shaving),
                                                     _sorter(sorter) {
    std::reverse(_variables.begin(), _variables.end());
    // root = static_cast<FlatZincSpace*>(fg->clone());
    // root->postConstraints(fg->constraints, false);
    for (int i = 0; i < _curFlatZincSpace->iv.size(); i++) {
        if (_curFlatZincSpace->iv[i].assigned()) {
            continue;
        }
        _variables.emplace_back(VarType::Int, FlatZincVarArray::iv, i);
    }
    for (int i = 0; i < _curFlatZincSpace->bv.size(); i++) {
        if (_curFlatZincSpace->bv[i].assigned()) {
            continue;
        }
        _variables.emplace_back(VarType::Bool, FlatZincVarArray::bv, i);
    }
}

void ShavingAsset::runShavingPass(SearchController& control, StatusStatistics statisStatistics,
    CloneStatistics cloneStatistics, bool& hasReportedLiteral,
    const std::function<std::vector<Literal> (VarDescription&, FlatZincSpace*)> &literalExtractor) const {
    std::vector queue(_variables);
    _sorter->sort_variables(queue, _curFlatZincSpace);
    while (!queue.empty()) {
        if (control._optimumFound->load()) {
            control.thread_done();
            return;
        }
        auto vd = queue.back();
        queue.pop_back();

        for (auto literal : literalExtractor(vd, _curFlatZincSpace)) {
            if (control._optimumFound->load()) {
                return;
            }
            const auto clone = dynamic_cast<FlatZincSpace*>(_curFlatZincSpace->clone(cloneStatistics));
            literal.var.eq(clone, literal.value);
            const auto status = clone->status(statisStatistics);
            delete clone;
            if (status != SS_FAILED) {
                continue;
            }
            control.report_forbidden_literal(literal);
            hasReportedLiteral = true;
            literal.var.nq(_curFlatZincSpace, literal.value);
            auto root_status = _curFlatZincSpace->status(statisStatistics);
            // If variable can neither be equal or not equal, then the problem is unsatisfiable and we are done.
            if (root_status == SS_FAILED) {
                // The only way the non-search Shaving Asset can actually finish first is iff the problem is unsatisfiable and it is found.
                if (!control._optimumFound->exchange(true)) {
                    control._finishedAsset = _assetId;
                }
                return;
            }
        }

        _sorter->sort_variables(queue, _curFlatZincSpace);
    }
}
