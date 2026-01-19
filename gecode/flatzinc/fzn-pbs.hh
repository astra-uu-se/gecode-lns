// fzn-pbs.hh

#ifndef FZN_PBS_HH
#define FZN_PBS_HH

// Includes
#include <gecode/flatzinc.hh>
#include <gecode/flatzinc/branch.hh>
#include <gecode/search.hh>
#include <gecode/flatzinc/searchenginebase.hh>

#include <memory>
#include <atomic>
#include <vector>
#include <array>
#include <string>
#include <sstream>
#include <limits>
#include <unordered_set>
#include <bits/random.h>

using namespace std;
using namespace Gecode;
using namespace Gecode::FlatZinc;

class SearchController;  // Declaration
class BaseAsset;  // Declaration

struct AssetData {
    FlatZincSpace::AssetType type;
    bool useSelfSubsumingPropagators;
    bool useDependencyCuratedLns;
};

enum class VarType { Int, Bool };

enum class FlatZincVarArray { iv, iv_aux, bv, bv_aux, };

struct VarDescription {
    VarType type;
    FlatZincVarArray array;
    int position;

    VarDescription(VarType type, FlatZincVarArray array, int position) : type(type), array(array), position(position) {}
    
    VarDescription() = default;

    Gecode::IntVar int_variable(FlatZincSpace* s) const {
        assert(type == VarType::Int);
        switch (array) {
            default:
                GECODE_NEVER;
            case FlatZincVarArray::iv:
                return s->iv[position];
            case FlatZincVarArray::iv_aux:
                return s->iv_aux[position];
        }
    }

    Gecode::BoolVar bool_variable(FlatZincSpace* s) const {
        assert(type == VarType::Bool);
        switch (array) {
            default:
                GECODE_NEVER;
            case FlatZincVarArray::bv:
                return s->bv[position];
            case FlatZincVarArray::bv_aux:
                return s->bv_aux[position];
        }
    }

    bool is_assigned(FlatZincSpace* s) const {
        switch (type) {
            default:
                GECODE_NEVER;
            case VarType::Int:
                return int_variable(s).assigned();
            case VarType::Bool:
                return bool_variable(s).assigned();
        }
    }

    unsigned int size(FlatZincSpace* s) const {
        switch (type) {
            default:
                GECODE_NEVER;
            case VarType::Int:
                return int_variable(s).size();
            case VarType::Bool:
                return bool_variable(s).size();
        }
    }

    int min(FlatZincSpace* s) const {
        switch (type) {
            default:
                GECODE_NEVER;
            case VarType::Int:
                return int_variable(s).min();
            case VarType::Bool:
                return bool_variable(s).min();
        }
    }

    int max(FlatZincSpace* s) const {
        switch (type) {
            default:
                GECODE_NEVER;
            case VarType::Int:
                return int_variable(s).max();
            case VarType::Bool:
                return bool_variable(s).max();
        }
    }

    double afc(FlatZincSpace* s) const {
        switch (type) {
            default:
                GECODE_NEVER;
            case VarType::Int:
                return int_variable(s).afc();
            case VarType::Bool:
                return bool_variable(s).afc();
        }
    }

    auto bounds_literals(FlatZincSpace* s) const;
    auto domain_literals(FlatZincSpace* s) const;

    void eq(FlatZincSpace* s, int value) const {
        switch (type) {
            default:
                GECODE_NEVER;
            case VarType::Int:
                rel(*s, int_variable(s), IRT_EQ, value);
                break;
            case VarType::Bool:
                rel(*s, bool_variable(s), IRT_EQ, value);
                break;
        }
    }

    void nq(FlatZincSpace* s, int value) const {
        switch (type) {
            default:
                GECODE_NEVER;
            case VarType::Int:
                rel(*s, int_variable(s), IRT_NQ, value);
            break;
            case VarType::Bool:
                rel(*s, bool_variable(s), IRT_NQ, value);
            break;
        }
    }
};

struct Literal {
    VarDescription var;
    int value;

    Literal(const VarDescription& var, int value)
        : var(var),
          value(value) {
    }

    Literal() = default;

};

inline auto VarDescription::bounds_literals(FlatZincSpace* s) const {
    return std::vector{
        Literal(*this, min(s)),
        Literal(*this, max(s)),
    };
}

inline auto VarDescription::domain_literals(FlatZincSpace* s) const {
    switch (type) {
        default:
            GECODE_NEVER;
        case VarType::Int: {
            std::vector<Literal> result;
            IntVar v = int_variable(s);
            result.reserve(v.size());
            auto values = IntVarValues(v);
            while (values()) {
                result.emplace_back(*this, values.val());
                // result.emplace_back(Literal(*this, values.val()));
                ++values;
            }
            return result;
        }
        case VarType::Bool:
            return bounds_literals(s);
    }
}

class VariableSorter {
public:
    virtual ~VariableSorter() = default;

    /// Sort the variables, setting the most interesting variable last
    virtual void sort_variables(std::vector<VarDescription>& variables, FlatZincSpace* root) = 0;
};

class InputOrderVariableSorter : public VariableSorter {
public:
    void sort_variables(std::vector<VarDescription>& /*variables*/, FlatZincSpace* /*root*/) override {
        // No rearrangement
    }
};

class SmallestSizeVariableSorter : public VariableSorter {
public:
    void sort_variables(std::vector<VarDescription>&variables, FlatZincSpace* root) override {
        // Sort with smallest variables last
        std::sort(variables.begin(), variables.end(),
                  [root](const VarDescription&a, const VarDescription&b) {
                      return a.size(root) > b.size(root);
                  });
    }
};

class LargestAFCVariableSorter : public VariableSorter {
public:
    void sort_variables(std::vector<VarDescription>&variables, FlatZincSpace* root) override {
        // Sort with largest AFC last
        std::sort(variables.begin(), variables.end(),
                  [root](const VarDescription&a, const VarDescription&b) {
                      return a.size(root) < b.size(root);
                  });
    }
};
/// Multi armed bandit
class Bandit {
protected:
    size_t _totalCount{0};
    double _ucb{0.0};

    size_t _numArms;
    /// Often called epsilon
    double _temperature;
    std::vector<double> _totalReward;
    std::vector<double> _averageReward;
    std::vector<size_t> _armTotalCount;

    static size_t randomArm(std::vector<double>& weights);

public:
    explicit Bandit(size_t numArms, double temperature = 0.1, double learningRate = 0.1);

    virtual ~Bandit() = default;
    void updateReward(size_t arm, double reward);
    void updateRewardUCB(size_t arm, double reward, double beta=1.0);
    [[nodiscard]] size_t bestArm() const;
    [[nodiscard]] size_t randomArm() const;
    [[nodiscard]] size_t softMax(double tau = 0.1) const;
};


class AssetExecutor : public Gecode::Support::Runnable {
    /// The common controller for running tests
    SearchController& control;
    /// The running asset.
    BaseAsset* asset;
    // The options for the FlatZinc space and search.
    FlatZincOptions& fopt;
    // Printer (Stores the output variables)
    FlatZinc::Printer& p;
    // The asset for this search.
    unsigned int asset_id;
    // If run search or not.
    bool do_search;
    // Different runs depending on asset.
    void runSearch();
    void runShaving();

public:
    // Constructor
    AssetExecutor(SearchController& control, BaseAsset* asset, FlatZincOptions& fopt, unsigned int asset_id, bool do_search)
    : control(control), asset(asset), fopt(fopt), p(p), asset_id(asset_id), do_search(do_search) {}
    // Run the search.
    void run() override {do_search ? runSearch() : runShaving();};
};

class BaseAsset {
    protected:
    FlatZincSpace& _originalFlatZincSpace;
    FlatZincSpace* _curFlatZincSpace;
    FlatZincOptions& _flatZincOptions;
    StatusStatistics _statusStatistics;
    unsigned int _assetId;
    size_t _banditArmId;
    FlatZincSpace::AssetType _assetType;
    bool _useDependencyCuratedLns;
    bool _useSelfSubsumingPropagators;

    unsigned int _numPropagators{0};
    double _solveTime{0.0};
    size_t _numSolutions{0};
    string _assetStr{};

    BaseAsset(FlatZincSpace& flatZincSpace, FlatZincSpace* curFlatZincSpace, FlatZincOptions& flatZincOptions, unsigned int assetId,
        FlatZincSpace::AssetType, bool useDependencyCuratedLns = true, bool useSelfSubsumingPropegators = true);

    std::shared_ptr<Search::Options> generateSearchOptions(FlatZincSpace&, Search::Stop*) const;

    [[nodiscard]] bool sortFlatAnnotations() const;


public:
    BaseAsset(FlatZincSpace& flatZincSpace, FlatZincOptions& flatZincOptions) :
    BaseAsset(flatZincSpace, nullptr, flatZincOptions, 0, FlatZincSpace::AssetType::DUMMY) {}
    virtual ~BaseAsset() {
        delete _curFlatZincSpace;
        _curFlatZincSpace = nullptr;
        _assetStr.clear();
    }
    virtual void run() {}
    [[nodiscard]] virtual FlatZincSpace& flatZincSpace() const {
        return _originalFlatZincSpace;
    }
    [[nodiscard]] FlatZincSpace* curFlatZincSpace() const {
        return _curFlatZincSpace;
    }
    [[nodiscard]] virtual BaseEngine* engine() const {
        return nullptr;
    }
    [[nodiscard]] virtual unsigned int numPropagators() const {
        return _numPropagators;
    }
    [[nodiscard]] virtual double solveTime() const {
        return _solveTime;
    }
    [[nodiscard]] virtual StatusStatistics statusStatistics() const {
        return _statusStatistics;
    }
    [[nodiscard]] virtual long unsigned int shavingStart() const {
        return 0;
    }
    [[nodiscard]] virtual string assetTypeStr() const {
        return _assetStr;
    }
    [[nodiscard]] virtual Search::Options& searchOptions() const {
        throw std::runtime_error("getSearchOptions not supported on this asset type.");
    }
    [[nodiscard]] virtual FlatZincSpace::AssetType assetType() const {
        return _assetType;
    }
    [[nodiscard]] virtual int numThreads() const {
        return 1;
    }
    virtual void setNumPropagators(unsigned int numPropagators) {
        _numPropagators = numPropagators;
    }
    virtual void setStatusStatistics(StatusStatistics statusStatistics) {
        _statusStatistics = statusStatistics;
    }
    virtual void setShavingStart(long unsigned int) {}
    virtual void setAssetTypeStr(const string& assetStr) {
        _assetStr = assetStr;
    }
    virtual void setEngine(BaseEngine*) {}

    virtual void increaseSolveTime(double time) {
        _solveTime += time;
    }
    [[nodiscard]] bool oppositeBranching() const;
    [[nodiscard]] bool pbsBranching() const;
    [[nodiscard]] virtual int banditArmId() const { return -1; };
    virtual void updateBanditArmId() {};
    [[nodiscard]] virtual bool runNextRound() const;
    virtual void updateEngine() {};
    [[nodiscard]] size_t numSolutions() const { return _numSolutions; }
    virtual size_t incrSolutions(size_t increment) { return _numSolutions += increment; }
};

class DFSAsset : public BaseAsset {
    public:
        DFSAsset(SearchController& searchController, FlatZincSpace& fg, FlatZincOptions& fopt,
            unsigned int assetId, FlatZincSpace::AssetType assetType, unsigned int numThreads,
            bool useSelfSubsumingPropagators = true);

    ~DFSAsset() override {
            delete _engine;
            _engine = nullptr;
            if (_branchModifier.pbs_variable_branchings != nullptr){
                delete _branchModifier.pbs_variable_branchings;
                _branchModifier.pbs_variable_branchings = nullptr;
            }
            if (_searchOptions != nullptr) {
                delete _searchOptions->stop;
                delete _searchOptions->tracer;
            }
        }

        void run() override {Gecode::Support::Thread::run(executor);};

        [[nodiscard]] long unsigned int shavingStart() const override { return _shavingStart; }

        [[nodiscard]] AssetExecutor* getExecutor() const { return executor; }
        
        void setShavingStart(long unsigned int start) override { _shavingStart = start; }

        void setEngine(BaseEngine* se) override { this->_engine = se; }

        [[nodiscard]] BaseEngine* engine() const override { return _engine; }

        [[nodiscard]] Search::Options& searchOptions() const override { return *_searchOptions; }

        SearchController& _searchController;

    private:
        unsigned int _numThreads;
        BranchModifier _branchModifier;
        AssetExecutor* executor;

        std::shared_ptr<Search::Options> _searchOptions{nullptr};
        BaseEngine* _engine{nullptr};
        long unsigned int _shavingStart{0};
};

class LNSAsset : public BaseAsset {
    public:
        LNSAsset(SearchController& searchController, FlatZincSpace& fg, FlatZincOptions& fopt,
            unsigned int assetId, FlatZincSpace::AssetType assetType, bool useSelfSubsumingPropagators = true,
            bool useDependencyCuratedLns = true, RestartMode restartMode = RM_LUBY, double restartBase = 1.5,
            unsigned int restartScale = 250);

        ~LNSAsset() override {
            delete _engine;
            _engine = nullptr;
            if (_branchModifier.pbs_variable_branchings != nullptr){
                delete _branchModifier.pbs_variable_branchings;
                _branchModifier.pbs_variable_branchings = nullptr;
            }
            // delete executor; executor = nullptr;
            if (_searchOptions != nullptr) {
                delete _searchOptions->stop;
                delete _searchOptions->tracer;
            }
        };

        void run() override {Gecode::Support::Thread::run(executor);};

        [[nodiscard]] BaseEngine* engine() const override { return _engine; }
        [[nodiscard]] long unsigned int shavingStart() const override { return _shavingStart; }
        [[nodiscard]] AssetExecutor* getExecutor() const { return executor; }
        [[nodiscard]] Search::Options& searchOptions() const override { return *_searchOptions; }

        void setShavingStart(long unsigned int start) override { _shavingStart = start; }
        void setEngine(BaseEngine* engine) override { this->_engine = dynamic_cast<RBSEngine*>(engine); }

        SearchController& _searchController;

    private:
        BranchModifier _branchModifier;
        RestartMode _restartMode;
        double _restartBase;
        unsigned int _restartScale;
        AssetExecutor* executor;
        std::shared_ptr<Search::Options> _searchOptions{nullptr};
        RBSEngine* _engine{nullptr};
    long unsigned int _shavingStart{0};
};

class BanditArmAsset : public BaseAsset {
public:
    BanditArmAsset(SearchController& searchController, FlatZincSpace& fg, FlatZincOptions& fopt,
        unsigned int assetId, RestartMode restartMode = RM_LUBY, double restartBase = 1.5,
        unsigned int restartScale = 250);

    ~BanditArmAsset() override {
        delete _engine;
        _engine = nullptr;
        if (_branchModifier.pbs_variable_branchings != nullptr){
            delete _branchModifier.pbs_variable_branchings;
            _branchModifier.pbs_variable_branchings = nullptr;
        }
        // delete executor; executor = nullptr;
        if (_searchOptions != nullptr) {
            delete _searchOptions->stop;
            delete _searchOptions->tracer;
        }
    };

    void run() override {Gecode::Support::Thread::run(executor);};

    [[nodiscard]] BaseEngine* engine() const override { return _engine; }
    [[nodiscard]] long unsigned int shavingStart() const override { return _shavingStart; }
    [[nodiscard]] AssetExecutor* getExecutor() const { return executor; }
    [[nodiscard]] Search::Options& searchOptions() const override { return *_searchOptions; }
    size_t incrSolutions(size_t increment) override {
        BaseAsset::incrSolutions(increment);
        _numCurSolutions += increment;
        return _numCurSolutions;
    }

    void setShavingStart(long unsigned int start) override { _shavingStart = start; }
    void setEngine(BaseEngine* engine) override { this->_engine = dynamic_cast<RBSEngine*>(engine); }
    void updateBanditArmId() override;
    [[nodiscard]] bool runNextRound() const override;
    void updateEngine() override;

    SearchController& _searchController;


private:
    BranchModifier _branchModifier;
    RestartMode _restartMode;
    double _restartBase;
    unsigned int _restartScale;
    AssetExecutor* executor;
    std::shared_ptr<Search::Options> _searchOptions{nullptr};
    RBSEngine* _engine{nullptr};
    long unsigned int _shavingStart{0};
    Support::Timer _timeout;

    const double defaultTime{5000};
    std::optional<double> time;
    size_t _banditTimestamp{std::numeric_limits<size_t>::max()};
    size_t _numCurSolutions{0};

};

class RoundRobinLNSAsset : public BaseAsset {
    public:
        RoundRobinLNSAsset(SearchController& control, FlatZincSpace& fg, FlatZincOptions& fopt,
            unsigned int asset_id);
        ;
        void run() override;

        [[nodiscard]] FlatZincSpace& flatZincSpace() const override { return best_asset->flatZincSpace(); }
        [[nodiscard]] BaseEngine* engine() const override { return best_asset->engine(); }
        [[nodiscard]] StatusStatistics statusStatistics() const override { return best_asset->statusStatistics(); }
        [[nodiscard]] unsigned int numPropagators() const override { return best_asset->numPropagators(); }
        [[nodiscard]] double solveTime() const override { return best_asset->solveTime(); }
        [[nodiscard]] string assetTypeStr() const override { return best_asset->assetTypeStr(); }
        [[nodiscard]] Search::Options& searchOptions() const override { return best_asset->searchOptions(); }
        [[nodiscard]] FlatZincSpace::AssetType assetType() const override { return best_asset->assetType(); }

        void setNumPropagators(unsigned int n_p) override { best_asset->setNumPropagators(n_p); }
        void setStatusStatistics(StatusStatistics statisStatistics) override { best_asset->setStatusStatistics(statisStatistics); }
        void setEngine(BaseEngine* se) override { best_asset->setEngine(se); }

        void increaseSolveTime(double /*time*/) override {};

        std::unique_ptr<BaseAsset> best_asset;

    private:
        SearchController& control;
        std::vector<std::unique_ptr<LNSAsset>> _roundRobinAssets;
};

class ShavingAsset : public BaseAsset {
    public:
        ShavingAsset(SearchController& control, FlatZincSpace& fg, FlatZincOptions& fopt, unsigned int assetId, FlatZincSpace::AssetType assetType, int maxDomShavingSize, bool do_bounds_shaving, VariableSorter* sorter);

    ~ShavingAsset() override {
            delete _sorter;
            _sorter = nullptr;
        };

        void run() override {Gecode::Support::Thread::run(_executor);};
        void runShavingPass(SearchController& control, StatusStatistics statisStatistics, CloneStatistics cloneStatistics, bool& hasReportedLiteral, const std::function<std::vector<Literal> (VarDescription&, FlatZincSpace*)> &literalExtractor) const;
        
        [[nodiscard]] FlatZincSpace& flatZincSpace() const override { return *_curFlatZincSpace; }
        [[nodiscard]] bool doBoundsShaving() const { return _doBoundsShaving; }
        [[nodiscard]] int getMaxDomShavingSize() const { return _maxDomShavingSize; }
        [[nodiscard]] long unsigned int shavingStart() const override { return 0; }
        [[nodiscard]] double solveTime() const override { return 0; }

        SearchController& control;

    private:
        AssetExecutor* _executor;

        std::vector<VarDescription> _variables;
        int _maxDomShavingSize;
        bool _doBoundsShaving;
        VariableSorter* _sorter;
};

class SearchController {
public:
    // Methods
    SearchController(FlatZinc::FlatZincSpace* flatZincSpace, std::ostream& out, Printer& printer, FlatZincOptions& flatZincOptions, Support::Timer& timerTotal); // constructor
    ~SearchController(); // destructor
    bool init();
    void run();
    // Emplace forbidden literal.
    void report_forbidden_literal(Literal forbidden) { _forbiddenLiterals.push_back(forbidden); }
    std::vector<Literal> get_forbidden_literals() { return _forbiddenLiterals; }
    // Signals that a search for a thread is finished.
    void thread_done();

    FlatZincSpace::AssetType assetType(size_t armId, bool lockMutex = true);

    bool useSelfSubsumingPropagators(size_t armId, bool lockMutex = true);

    bool useDependencyCuratedLns(size_t armId, bool lockMutex = true);

    [[nodiscard]] size_t banditTimestamp() const {
        return _banditTimestamp;
    }

    // Variables
    // Intial search space.
    FlatZinc::FlatZincSpace* _flatZincSpace;
    FlatZincOptions& _flatZincOptions;
    StatusStatistics _statusStatistics;
    // The printer for the assets.
    FlatZinc::Printer& _printer;
    Support::Timer& _timerTotal;
    std::ostream& _ostream;
    // The number of assets.
    // Each asset controller by the controller.
    std::vector<std::unique_ptr<BaseAsset>> _assets;
    // The best solutions found during search.
    std::shared_ptr<std::vector<std::shared_ptr<Space>>> _allBestSolutions;
    // The current method.
    FlatZincSpace::Meth _method;
    // A mutex lock for updating best space.
    std::mutex _solutionMutex;
    // The number of solutions found by each asset.
    std::vector<int> _assetNumSolutions;
    // Flags if an asset has updated its search engine during search.
    std::vector<bool> _assetSwappedEngine;
    /// Flag indicating that the final best solution has been found.
    std::shared_ptr<std::atomic<bool>> _optimumFound{std::make_shared<std::atomic<bool>>(false)};

    // The asset that finished the search and found the solution.
    unsigned int _finishedAsset{std::numeric_limits<unsigned int>::max()};

    std::mutex _banditMutex;
    std::unique_ptr<Bandit> _bandit;

    bool updateBestSolution(const std::shared_ptr<FlatZincSpace> &sol, unsigned int asset_id);

    [[nodiscard]] int banditArmId(FlatZincSpace::AssetType assetType, bool useSelfSubsumingPropagators, bool useDependencyCuratedLns) const;

private:
    // Waits for all threads to be done.
    void awaitRunnersCompleted();
    // Creates the asset used by the portfolio.
    void createAsset(FlatZincSpace::AssetType asset, unsigned int assetId, bool useSelfSubsumingPropagators);

    [[nodiscard]] bool isValidBanditArm(FlatZincSpace::AssetType assetType, bool useSelfSubsumingPropagators,
                      bool useDependencyCuratedLns) const;

    void updateMultiArmedBandit();
    // Sets up the asset used by the portfolio.
    void createAssets(double initTime);
    // Gives the statistics of the solution. (TODO: Make it possible to output from all engines and/or spaces)
    void solutionStatistics(BaseAsset* asset, Support::Timer& t_total, unsigned int finished_asset);

    void createBanditArmAsset(unsigned int assetId);

    // Variables
    std::vector<std::array<std::array<int, 2>, 2>> _banditArmIds;
    std::vector<FlatZincSpace::AssetType> _armIdToAssetType;
    std::vector<bool> _armIdToSelfSubsuming;
    std::vector<bool> _armIdToCuratedDependency;
    /// Event for signaling that execution is done.
    Gecode::Support::Event _executionDoneEvent;
    /// The number of test runners that are to be set up.
    std::atomic<unsigned int> _runningThreads;
    /// Flag indicating some thread is waiting on the execution to be done.
    std::atomic<bool> _executionDoneWaitStarted{false};
    // Literals that are forbidden in the search.
    std::vector<Literal> _forbiddenLiterals{0};
    size_t _banditTimestamp{0};
    
};

// }} 
#endif // FZN_PBS_HH