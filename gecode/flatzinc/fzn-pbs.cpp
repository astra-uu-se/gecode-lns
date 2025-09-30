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
      _incumbentSolution(std::make_shared<IncumbentSolution>()),
      _allBestSolutions(std::make_shared<std::vector<std::shared_ptr<Space>>>()) {}

SearchController::~SearchController() {
    if (_allBestSolutions != nullptr) {
        _allBestSolutions->clear();
    }
    _allBestSolutions = nullptr;
}

void SearchController::thread_done() {
    if (_runningThreads.fetch_sub(1) == 1) {
        _executionDoneEvent.signal();
    }
}

bool SearchController::updateBestSolution(const std::shared_ptr<FlatZincSpace> &sol,
                                          unsigned int asset_id) {
    // If the optimum was found, then stop there is no need to update the best solution.
    for (int i = 0; i < sol->iv.size(); ++i) {
        assert(sol->iv[i].width() == 1);
    }

    _solutionMutex.lock();
    if (_optimumFound->load()){
        _solutionMutex.unlock();
        return false;
    }

    const auto expected = _incumbentSolution->load();
    const bool solIsBetter = expected == nullptr || sol->compareObjectiveValue(*expected) < 0;
    if (solIsBetter) {
        // Critical Section
        const bool success = _incumbentSolution->compare_exchange_strong(expected, sol);
        assert(success);
        if (success){
            _allBestSolutions->emplace_back(std::dynamic_pointer_cast<Gecode::Space>(sol));
            if (_flatZincOptions.allSolutions()){
                sol->print(_ostream, _printer);
                _ostream << "----------" << std::endl;
            }
            if (_method == FlatZincSpace::SAT){
                _optimumFound->store(true);
            }
            if (asset_id < _assets.size()) {
                _assetNumSolutions[asset_id]++;
                _finishedAsset = asset_id;
            }
        }
    }
    _solutionMutex.unlock();

    return solIsBetter;
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
    if (_finishedAsset == -1){
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
    if (_flatZincOptions.fullStatistics()){
        const FlatZincSpace* const fzs = asset->flatZincSpace();
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
            << (fzs->getintVarCount() + fzs->getboolVarCount() + fzs->getsetVarCount()) << std::endl
            << "%%%mzn-stat: propagators=" << numPropagators << std::endl
            << "%%%mzn-stat: propagations=" << statusStatistics.propagate+stat.propagate << std::endl
            << "%%%mzn-stat: nodes=" << stat.node << std::endl
            << "%%%mzn-stat: failures=" << stat.fail << std::endl
            << "%%%mzn-stat: restarts=" << stat.restart << std::endl
            << "%%%mzn-stat: peakDepth=" << stat.depth << std::endl
            << "%%%mzn-stat-end" << std::endl
            << std::endl;

        for (long unsigned int a = 0; a < _assets.size(); a++){
            if (static_cast<int>(a) == _finishedAsset){
                continue;
            }
            numPropagators = _assets[a]->numPropagators();
            if (_assets[a]->assetType() == AssetType::SHAVING){
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
            _ostream << "%%%mzn-stat: propagators=" << numPropagators << std::endl
                << "%%%mzn-stat: propagations=" << statusStatistics.propagate+stat.propagate << std::endl
                << "%%%mzn-stat: nodes=" << stat.node << std::endl
                << "%%%mzn-stat: failures=" << stat.fail << std::endl
                << "%%%mzn-stat: restarts=" << stat.restart << std::endl
                << "%%%mzn-stat: peakDepth=" << stat.depth << std::endl
                << "%%%mzn-stat-end" << std::endl
                << std::endl;
        }
        for (long unsigned int i = 0; i < _assetNumSolutions.size(); i++){
            _ostream << "%%%mzn-stat: asset " << _assets[i]->assetTypeStr() << " found " << _assetNumSolutions[i] << " solutions." << endl;
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

void SearchController::createAsset(AssetType asset, unsigned int assetId, unsigned int threads) {
    switch (asset)
    {
    case AssetType::SHAVING:
        _assets[assetId] = (std::make_unique<ShavingAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, 20, true, new LargestAFCVariableSorter()));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("shaving asset");
        }
        break;
    case AssetType::USER:
        _assets[assetId] = (std::make_unique<DFSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, false, false, _flatZincOptions.c_d(), _flatZincOptions.a_d(), threads));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("bab asset");
        }
        break;
    case AssetType::LNS_USER:
        _assets[assetId] = (std::make_unique<LNSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, false, false, FlatZincSpace::LNSType::RANDOM, _flatZincOptions.c_d(), _flatZincOptions.a_d(), threads, RM_LUBY, 1.5, 250));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("random lns asset");
        }
        break;
    case AssetType::PGLNS:
        _assets[assetId] = (std::make_unique<LNSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, false, false, FlatZincSpace::LNSType::PG, _flatZincOptions.c_d(), _flatZincOptions.a_d(), threads, RM_LUBY, 1.5, 250));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("propagation guided lns asset");
        }
        break;
    case AssetType::CIGLNS:
        _assets[assetId] = (std::make_unique<LNSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, true, false, FlatZincSpace::LNSType::CIG, _flatZincOptions.c_d(), _flatZincOptions.a_d(), threads, RM_LUBY, 1.5, 250));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("cost impact guided lns asset");
        }
        break;
    case AssetType::OBJRELLNS:
        _assets[assetId] = (std::make_unique<LNSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, false, false, FlatZincSpace::LNSType::OBJREL, _flatZincOptions.c_d(), _flatZincOptions.a_d(), threads, RM_LUBY, 1.5, 250));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("objective relaxation lns asset");
        }
        break;
    case AssetType::SVRLNS:
        _assets[assetId] = (std::make_unique<LNSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, false, false, FlatZincSpace::LNSType::SVR, _flatZincOptions.c_d(), _flatZincOptions.a_d(), threads, RM_LUBY, 1.5, 250));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("static variable dependency lns asset");
        }
        break;
    case AssetType::REVPGLNS:
        _assets[assetId] = (std::make_unique<LNSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, false, false, FlatZincSpace::LNSType::rPG, _flatZincOptions.c_d(), _flatZincOptions.a_d(), threads, RM_LUBY, 1.5, 250));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("reversed propagation guided lns asset");
        }
        break;
    case AssetType::PB_USER:
        _assets[assetId] = (std::make_unique<DFSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, false, false, true, _flatZincOptions.c_d(), _flatZincOptions.a_d(), _flatZincOptions.threads()));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("prioritized branching bab asset");
        }
        break;
    case AssetType::USER_OPPOSITE:
        _assets[assetId] = (std::make_unique<DFSAsset>(*this, _flatZincSpace, _flatZincOptions, assetId, asset, true, false, false, _flatZincOptions.c_d(), _flatZincOptions.a_d(), _flatZincOptions.threads()));
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[assetId]->setAssetTypeStr("bab opposite branching asset");
        }
        break;
    default:
        break;
    }
}

void SearchController::createAssets(double initTime) {
    // Vector of asset type and the number of threads to use for that asset type.
    vector<pair<AssetType,int>> asset_types;
    unsigned int assets_to_create{0};

    // Select the assets to use depending on method, number of solutions required and number of threads available.
    // The order of the assets in the vector is the order of priority (Given from the results of the thesis).
    // It also makes sense not to use LNS as the first assets to be created, as they need a solution to function properly (even though the time difference is extremely small).
    if (_flatZincSpace->method() == FlatZincSpace::SAT){
        asset_types = {pair(AssetType::USER, 1), pair(AssetType::PB_USER, 1), pair(AssetType::USER_OPPOSITE, 1), pair(AssetType::SHAVING, 1)};

        // If the ability to add more than one solution is to be added, then these asset orders should be used:
        // if (fopt.solutions() > 1){
        //     // If more solutions than one is requested, then use the best performing LNS asset according to the statistics seen in thesis (Cost Impact Guided).
        //     asset_types = {pair(USER, 1), pair(PB_USER, 1), pair(USER_OPPOSITE, 1), pair(CIGLNS,1), pair(SHAVING, 1)};
        // }
        // else{
        //     // LNS is not used for single solution search.
        //     asset_types = {pair(USER, 1), pair(PB_USER, 1), pair(USER_OPPOSITE, 1), pair(SHAVING, 1)};
        // }
    }
    else if (0 <= _flatZincOptions.pbsAssetType() && _flatZincOptions.pbsAssetType() <= 9){
        asset_types = {pair(static_cast<AssetType>(_flatZincOptions.pbsAssetType()), 1)};
    }
    else{
        // If optimization problem, then use all available search assets.
        asset_types = {pair(AssetType::USER, 1), pair(AssetType::PB_USER, 1), pair(AssetType::USER_OPPOSITE, 1), pair(AssetType::CIGLNS, 1), pair(AssetType::OBJRELLNS, 1), pair(AssetType::SVRLNS, 1), pair(AssetType::PGLNS, 1), pair(AssetType::REVPGLNS, 1), pair(AssetType::LNS_USER, 1), pair(AssetType::SHAVING, 1)};

    }

    // Choose the number of assets to create based on the number of threads available.
    if (_flatZincOptions.threads() > asset_types.size()){
        assets_to_create = asset_types.size();
        for (size_t i = 0; i < asset_types.size(); ++i) {
            if (asset_types[i].first == AssetType::USER) {
                asset_types[i] = pair(AssetType::USER, _flatZincOptions.threads() - assets_to_create + 1);
                break;
            }
        }
    }
    else{
        assets_to_create = _flatZincOptions.threads();
    }

    // Set array sizes indexed by the assets id.
    _assets.resize(assets_to_create);
    _assetNumSolutions.resize(assets_to_create);
    _assetSwappedEngine.resize(assets_to_create, false);
    _runningThreads = assets_to_create;

    // Create the assets.
    for (int asset = 0; asset < assets_to_create; asset++) {
        createAsset(asset_types[asset].first, asset, asset_types[asset].second);
        _assets[asset]->increaseSolveTime(initTime);
        _assets[asset]->setStatusStatistics(_statusStatistics);
    }
    if (_flatZincOptions.fullStatistics()) {
        _ostream << "%%%mzn-stat: created " << assets_to_create << " asset(s):" << std::endl;
        for (size_t i = 0; i < assets_to_create; ++i) {
            const auto s = asset_types[i].first == AssetType::USER ? "USER" : (
                        asset_types[i].first == AssetType::LNS_USER ? "LNS_USER" : (
                        asset_types[i].first == AssetType::PGLNS ? "PGLNS" : (
                        asset_types[i].first == AssetType::CIGLNS ? "CIGLNS" : (
                        asset_types[i].first == AssetType::OBJRELLNS ? "OBJRELLNS" : (
                        asset_types[i].first == AssetType::SVRLNS ? "SVRLNS" : (
                        asset_types[i].first == AssetType::REVPGLNS ? "REVPGLNS" : (
                        asset_types[i].first == AssetType::PB_USER ? "PB_USER" : (
                        asset_types[i].first == AssetType::USER_OPPOSITE ? "USER_OPPOSITE" : (
                        asset_types[i].first == AssetType::SHAVING ? "SHAVING" : (
                        asset_types[i].first == AssetType::DUMMY ? "DUMMY" : "UNKNOWN"))))))))));
            _ostream << "%%%mzn-stat:  asset " << s << " using " << asset_types[i].second << " thread(s)" << std::endl;
        }
    }
}

// The controller that creates the workers and controls the searches.
bool SearchController::init() {
    Support::Timer propTimer;
    propTimer.start();
    const SpaceStatus preSearchProp = _flatZincSpace->status(_statusStatistics);
    const double initTime = propTimer.stop();
    // Make search space clone-able by calling status on it. If it fails, then the model is unsatisfiable.
    // If the space is unsatisfiable before the search even starts, then finish and print statistics through dummy asset.
    if (preSearchProp == SS_FAILED) {
        _ostream << "=====UNSATISFIABLE=====" << std::endl;
        // Create dummy asset so that information about UNSAT space can be printed out:
        _assets[0] = std::make_unique<BaseAsset>(_flatZincSpace, _flatZincOptions);
        _assets[0]->setStatusStatistics(_statusStatistics);
        _assets[0]->increaseSolveTime(initTime);
        if (_flatZincOptions.mode() == SM_STAT) {
            _assets[0]->setAssetTypeStr("none");
            solutionStatistics(_assets[0].get(), _timerTotal, -1);
        }
        return false;
    }

    // Populate the initial solution
    if (_flatZincSpace->hasInitialIncumbentSolution()) {
        auto* clone = _flatZincSpace->deepClone(_incumbentSolution, _optimumFound);
        auto bm = BranchModifier(false, false, false);
        clone->applyInitialIncumbentSolution();
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
    if (_finishedAsset < _assets.size() && _assets[_finishedAsset]->assetType() == AssetType::SHAVING){
        _ostream << "=====UNSATISFIABLE=====" << std::endl;
    } else {
        // Print the best or final solution:
        const auto sol = _incumbentSolution->load();
        // Not a guarantee that a solution is found and finished asset it set.
        // Use default user asset in case no solution was found.
        BaseEngine* se = _assets[_finishedAsset > _assets.size() ? 0 : _finishedAsset]->engine();

        if (sol) {
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
        else if (!sol) {
            _ostream << "=====UNKNOWN=====" << std::endl;
        }
    }
    // If print Statistics:
    if (_flatZincOptions.mode() == SM_STAT) {
        solutionStatistics(_assets[_finishedAsset].get(), _timerTotal, _finishedAsset);
    }

    // Delete allocated arrays in fzs.
    _flatZincSpace->deletePBSArrays();
}


// ########################################################################
//                         AssetExecutor below.
// ########################################################################
void AssetExecutor::runSearch(){
    const bool printAll = fopt.allSolutions();
    BaseEngine* engine = asset->engine();
    StatusStatistics statusStatistics = asset->statusStatistics();
    // Start the search timer.
    Support::Timer t_solve;
    t_solve.start();
    if (asset->flatZincSpace()->status(statusStatistics) == SS_FAILED) {
        control.thread_done();
        return;
    }
    asset->setNumPropagators(PropagatorGroup::all.size(*(asset->flatZincSpace())));
    asset->setStatusStatistics(statusStatistics);
    // Run the search engine.
    assert(engine != nullptr);
    std::shared_ptr<FlatZincSpace> sol;
    bool solWasBestSol = false;

    while (auto nextSol = std::shared_ptr<FlatZincSpace>(engine->next())) {
        const auto stat = nextSol->status();
        if (control._optimumFound->load()) {
            break;
        }
        // If last solution was not the current best solution, delete it.
        if (!solWasBestSol && sol != nullptr){
            sol = nullptr;
        }
        sol = nextSol;

        // If a solution is found, then all assets can stop their search
        // As the problem has been satisfied.
        if (control._method == FlatZincSpace::SAT){
            control._solutionMutex.lock();
            if (control._optimumFound->load()){
                control._solutionMutex.unlock();
                break;
            }
            control._optimumFound->store(true);
            control._incumbentSolution->store(sol);
            control._assetNumSolutions[asset_id]++;
            control._finishedAsset = asset_id;
            solWasBestSol = true;
            control._solutionMutex.unlock();
            break;
        }

        // TODO: Make sure that search did not finish due to LNS restart limit reached etc.
        // If one asset finished, stop looking for more solutions.
        solWasBestSol = control.updateBestSolution(sol, asset_id);

        // Apply nq constraints to make asset take advantage of shaving.
        std::vector<Literal> local_forbidden_literals = control.get_forbidden_literals();
        const size_t size = local_forbidden_literals.size();
        if (size > asset->shavingStart()){
            for (size_t i = asset->shavingStart(); i < size; i++){
                local_forbidden_literals[i].var.nq(asset->flatZincSpace(), local_forbidden_literals[i].value);
            }
        }

        // Change the search engine to update cd and ad.
        auto stats = engine->statistics();
        if (!control._assetSwappedEngine[asset_id] && stats.depth > 50){
            Search::Options searchOptions = asset->searchOptions();
            searchOptions.c_d = searchOptions.c_d * stats.depth;
            searchOptions.a_d = searchOptions.a_d * 2;

            delete engine;
            if (asset->lnsType() != FlatZincSpace::LNSType::NONE){
                fopt.restart(RM_LUBY);
                fopt.restart_base(1.5);
                fopt.restart_scale(250);
                searchOptions.cutoff = new Search::CutoffAppend(new Search::CutoffConstant(0), 1, Driver::createCutoff(fopt));
                auto* upd_se = new RBSEngine(asset->flatZincSpace(), searchOptions);
                asset->setEngine(dynamic_cast<BaseEngine*>(upd_se));
                engine = upd_se;
            } else {
                if (control._method == FlatZincSpace::SAT)
                {
                    auto* upd_se = new DFSEngine(asset->flatZincSpace(), searchOptions);
                    asset->setEngine(dynamic_cast<BaseEngine*>(upd_se));
                    engine = upd_se;
                }
                else
                {
                    auto* upd_se = new BABEngine(asset->flatZincSpace(), searchOptions);
                    asset->setEngine(dynamic_cast<BaseEngine*>(upd_se));
                    engine = upd_se;
                }
            }
            control._assetSwappedEngine[asset_id] = true;
        }
    }
    // Stop the search timer.
    const double t = t_solve.stop();
    asset->increaseSolveTime(t);
    control.thread_done();
}

// Go through and run each asset in the round robin for some fixed amount of restarts. Store the number of sols for each asset, best asset keeps on running until search finishes.
void RoundRobinLNSAsset::run(){
    int curBestObj = control._method == FlatZincSpace::MAX ? std::numeric_limits<int>::min() : std::numeric_limits<int>::max();

    const int optVar = _roundRobinAssets[0]->flatZincSpace()->optVar();
    Support::Timer t_solve;
    const bool printAll = _flatZincOptions.allSolutions();

    for (long unsigned int i = 0; i < _roundRobinAssets.size(); i++){
        // Do one run of the asset and decide which asset is the best.
        BaseEngine *se = _roundRobinAssets[i]->engine();
        t_solve.start();
        auto sol = std::shared_ptr<FlatZincSpace>(se->next());
        _roundRobinAssets[i]->increaseSolveTime(t_solve.stop());

        control.updateBestSolution(sol, _assetId);

        const int curObj = sol->iv[optVar].val();
        if (control._method == FlatZincSpace::MAX){
            if (curObj > curBestObj){
                curBestObj = curObj;
                best_asset = std::move(_roundRobinAssets[i]);
            }
        }
        else {
            if (curObj < curBestObj){
                curBestObj = curObj;
                best_asset = std::move(_roundRobinAssets[i]);
            }
        }

        if (_flatZincOptions.mode() == SM_STAT){
            switch (best_asset->lnsType())
            {
                case FlatZincSpace::LNSType::RANDOM:
                    best_asset->setAssetTypeStr("round robin asset random lns");
                    break;
                case FlatZincSpace::LNSType::PG:
                    best_asset->setAssetTypeStr("round robin asset propagation guided lns");
                    break;
                case FlatZincSpace::LNSType::rPG:
                    best_asset->setAssetTypeStr("round robin asset reversed propagation guided lns");
                    break;
                case FlatZincSpace::LNSType::OBJREL:
                    best_asset->setAssetTypeStr("round robin asset objective relaxation lns");
                    break;
                case FlatZincSpace::LNSType::CIG:
                    best_asset->setAssetTypeStr("rounds robin asset cost impact guided lns");
                    break;
                case FlatZincSpace::LNSType::SVR:
                    best_asset->setAssetTypeStr("round robin asset static variable relationship lns");
                    break;
                case FlatZincSpace::LNSType::NONE:
                    best_asset->setAssetTypeStr("round robin asset");
                    break;
            }
        }

        // If search is finished (solution has been found, then return (since we are done))
        if (control._optimumFound->load()){
            // Select any asset as solution has already been found.
            best_asset = std::move(_roundRobinAssets[i]);
            control.thread_done();
            return;
        }
    }
    // Unless search has finished, use the best engine and perform actual search:
    if (!control._optimumFound->load()){
        // If no solution was found.
        if (best_asset != nullptr){
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
    if (asset->flatZincSpace()->status(status_stat) != SS_FAILED) {
        asset->setNumPropagators(PropagatorGroup::all.size(*(asset->flatZincSpace())));
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

Search::Options BaseAsset::generateSearchOptions(FlatZincSpace* fzs, Search::Stop* stop) const {
    Search::Options searchOptions;
    searchOptions.stop = stop;
    searchOptions.c_d = _copyRecomputationDistance;
    searchOptions.a_d = _adaptiveRecomputationDistance;

#ifdef GECODE_HAS_FLOAT_VARS
    fzs->step = _flatZincOptions.step();
#endif

    searchOptions.numThreads = _numThreads;
    searchOptions.nogoods_limit = _flatZincOptions.nogoods() ? _flatZincOptions.nogoods_limit() : 0;

    if (_flatZincOptions.restart() != RM_NONE){
        _flatZincOptions.restart(RM_NONE);
    }

    auto* fznCutoff = Driver::createCutoff(_flatZincOptions);
    if (fznCutoff == nullptr) {
        searchOptions.cutoff = new Search::CutoffConstant(0);
    } else {
        searchOptions.cutoff = new Search::CutoffAppend(new Search::CutoffConstant(0), 1, fznCutoff);
    }
    if (_flatZincOptions.interrupt()) {
        Driver::PBSCombinedStop::installCtrlHandler(true);
    }
    return searchOptions;
}

DFSAsset::DFSAsset(SearchController &searchController, FlatZincSpace *fg, FlatZincOptions &fopt,
    unsigned int assetId, AssetType assetType, bool oppositeBranching, bool pbsBranching,
    bool sortFlatAnn, unsigned int copyRecomputationDistance, unsigned int adaptiveRecomputationDistance,
    unsigned int threads) :
BaseAsset(fg, fopt, assetId, assetType, copyRecomputationDistance, adaptiveRecomputationDistance, _numThreads),
_searchController(searchController),
_branchModifier(oppositeBranching, pbsBranching, sortFlatAnn),
executor(new AssetExecutor(searchController, this, fopt, assetId, true)),
_curFlatZincSpace(_flatZincSpace->deepClone(searchController._incumbentSolution, searchController._optimumFound)) {
    _curFlatZincSpace->postConstraints(_flatZincSpace->constraints, 7 <= _assetId && _assetId <= 8);
    if (_assetId == 7) {
        _branchModifier.use_pbs_branching = !_flatZincSpace->solveAnnotations();
        if (_branchModifier.use_pbs_branching){
            _branchModifier.PBAssetBranching(_flatZincSpace->constraints);
        }
    }

    _curFlatZincSpace->createBranchers(searchController._printer, _curFlatZincSpace->solveAnnotations(), _flatZincOptions, false, _branchModifier, std::cerr);
    _curFlatZincSpace->populateLnsVars(_flatZincSpace->constraints);

    _searchOptions = generateSearchOptions(_flatZincSpace, Driver::PBSCombinedStop::create(_flatZincOptions.node(), _flatZincOptions.fail(), _flatZincOptions.time(), 0, true, _searchController._optimumFound));
    _searchOptions.nogoods_limit = _flatZincOptions.nogoods() ? _flatZincOptions.nogoods_limit() : 0;
    _searchOptions.cutoff = new Search::CutoffAppend(new Search::CutoffConstant(0), 1, Driver::createCutoff(_flatZincOptions));

    if (_flatZincOptions.interrupt()) {
        Driver::PBSCombinedStop::installCtrlHandler(true);
    }

    if (searchController._method == FlatZincSpace::SAT)
    {
        _engine = new DFSEngine(_curFlatZincSpace, _searchOptions);
    }
    else
    {
        _engine = new BABEngine(_curFlatZincSpace, _searchOptions);
    }
}

LNSAsset::LNSAsset(SearchController &searchController, FlatZincSpace *fg, FlatZincOptions &fopt,
    unsigned int assetId, AssetType assetType, bool oppositeBranching, bool pbsBranching,
    bool sortFlatAnnotations, FlatZinc::FlatZincSpace::LNSType lnsType, unsigned int copyRecompuatationDistance,
    unsigned int adaptiveRecomputationDistance, unsigned int threads, RestartMode restartMode, double restartBase,
    unsigned int restartScale)
: BaseAsset(fg, fopt, assetId, assetType, copyRecompuatationDistance, adaptiveRecomputationDistance, _numThreads),
_searchController(searchController),
_branchModifier(oppositeBranching, pbsBranching, sortFlatAnnotations),
_restartMode(restartMode),
_restartBase(restartBase),
_restartScale(restartScale),
_lnsType(lnsType),
executor(new AssetExecutor(searchController, this, fopt, assetId, true)),
_curFlatZincSpace(_flatZincSpace->deepClone(searchController._incumbentSolution, searchController._optimumFound)) {
    _curFlatZincSpace->setLNSType(_lnsType);

    if (_flatZincOptions.interrupt()) {
        Driver::PBSCombinedStop::installCtrlHandler(true);
    }

    // Setup branching strategies for the asset before creating the branchers.
    _curFlatZincSpace->postConstraints(_flatZincSpace->constraints, _assetId <= 6);

    // If not RBS but asset is to use it:
    if (_flatZincOptions.restart() == RM_NONE){
        _flatZincOptions.restart(_restartMode);
        _flatZincOptions.restart_base(_restartBase);
        _flatZincOptions.restart_scale(_restartScale);
    }

    _searchOptions = generateSearchOptions(_curFlatZincSpace, Driver::PBSCombinedStop::create(_flatZincOptions.node(), _flatZincOptions.fail(), _flatZincOptions.time(), _flatZincOptions.restart_limit(), true, searchController._optimumFound));
    _curFlatZincSpace->createBranchers(searchController._printer, _flatZincSpace->solveAnnotations(), _flatZincOptions, false, _branchModifier, std::cerr);
    _curFlatZincSpace->populateLnsVars(_flatZincSpace->constraints);

    _engine = new RBSEngine(_curFlatZincSpace, _searchOptions, searchController._optimumFound, searchController._allBestSolutions);
}

RoundRobinLNSAsset::RoundRobinLNSAsset(SearchController &control, FlatZincSpace *fg, FlatZincOptions &fopt,
    unsigned int asset_id, unsigned int copyRecomputationDistance,
    unsigned int adaptiveRecompuatationDistance, unsigned int numThreads) :
BaseAsset(fg, fopt, asset_id, AssetType::DUMMY, copyRecomputationDistance, adaptiveRecompuatationDistance, numThreads),
best_asset(nullptr), control(control) {
    // Fill the round_robin_assets vector with all types of LNS assets available.
    // Ordering of assets can help (Now following thesis results).
    const auto assets = std::vector<std::pair<AssetType, FlatZincSpace::LNSType>>{
        {AssetType::CIGLNS, FlatZincSpace::LNSType::CIG},
        {AssetType::OBJRELLNS, FlatZincSpace::LNSType::OBJREL},
        {AssetType::SVRLNS, FlatZincSpace::LNSType::SVR},
        {AssetType::LNS_USER, FlatZincSpace::LNSType::RANDOM},
        {AssetType::PGLNS, FlatZincSpace::LNSType::PG},
        {AssetType::REVPGLNS, FlatZincSpace::LNSType::rPG}};
    for (const auto& [assetType, lnsType] : assets) {
        _roundRobinAssets.emplace_back(std::make_unique<LNSAsset>(control, _flatZincSpace, _flatZincOptions,
            asset_id, assetType, false, false,
            true, lnsType, _copyRecomputationDistance,
            _adaptiveRecomputationDistance, _numThreads, RM_LUBY, 1.5, 250));
    }
}

ShavingAsset::ShavingAsset(SearchController &control, FlatZincSpace *fg, FlatZincOptions &fopt,
    unsigned int assetId, AssetType assetType, int maxDomShavingSize,
    bool do_bounds_shaving, VariableSorter *sorter): BaseAsset(fg, fopt, assetId, assetType, 0, 0, 0),
                                                     control(control),
                                                     _executor(new AssetExecutor(control, this, fopt, assetId, false)),
                                                     _maxDomShavingSize(maxDomShavingSize),
                                                     _doBoundsShaving(do_bounds_shaving),
                                                     _sorter(sorter) {
    std::reverse(_variables.begin(), _variables.end());
    // root = static_cast<FlatZincSpace*>(fg->clone());
    _rootFlatZincSpace = _flatZincSpace;
    // root->postConstraints(fg->constraints, false);
    for (int i = 0; i < _rootFlatZincSpace->iv.size(); i++) {
        if (_rootFlatZincSpace->iv[i].assigned()) {
            continue;
        }
        _variables.emplace_back(VarType::Int, FlatZincVarArray::iv, i);
    }
    for (int i = 0; i < _rootFlatZincSpace->bv.size(); i++) {
        if (_rootFlatZincSpace->bv[i].assigned()) {
            continue;
        }
        _variables.emplace_back(VarType::Bool, FlatZincVarArray::bv, i);
    }
}

void ShavingAsset::runShavingPass(SearchController& control, StatusStatistics statisStatistics,
    CloneStatistics cloneStatistics, bool& hasReportedLiteral,
    const std::function<std::vector<Literal> (VarDescription&, FlatZincSpace*)> &literalExtractor) const {
    std::vector queue(_variables);
    _sorter->sort_variables(queue, _rootFlatZincSpace);
    while (!queue.empty()) {
        if (control._optimumFound->load()) {
            control.thread_done();
            return;
        }
        auto vd = queue.back();
        queue.pop_back();

        for (auto literal : literalExtractor(vd, _rootFlatZincSpace)) {
            if (control._optimumFound->load()) {
                return;
            }
            const auto clone = dynamic_cast<FlatZincSpace*>(_rootFlatZincSpace->clone(cloneStatistics));
            literal.var.eq(clone, literal.value);
            const auto status = clone->status(statisStatistics);
            delete clone;
            if (status != SS_FAILED) {
                continue;
            }
            control.report_forbidden_literal(literal);
            hasReportedLiteral = true;
            literal.var.nq(_rootFlatZincSpace, literal.value);
            auto root_status = _rootFlatZincSpace->status(statisStatistics);
            // If variable can neither be equal or not equal, then the problem is unsatisfiable and we are done.
            if (root_status == SS_FAILED) {
                // The only way the non-search Shaving Asset can actually finish first is iff the problem is unsatisfiable and it is found.
                if (!control._optimumFound->exchange(true)){
                    control._finishedAsset = _assetId;
                }
                return;
            }
        }

        _sorter->sort_variables(queue, _rootFlatZincSpace);
    }
}
