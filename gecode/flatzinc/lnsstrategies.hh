#ifndef LNSSTRATEGIES_HH
#define LNSSTRATEGIES_HH

// Includes
#include <gecode/flatzinc.hh>
#include <gecode/flatzinc/branch.hh>
#include <gecode/search.hh>
#include <gecode/flatzinc/searchenginebase.hh>

#include <memory>
#include <vector>
#include <array>
#include <string>
#include <sstream>
#include <limits>
#include <unordered_set>

using namespace std;
using namespace Gecode;
using namespace Gecode::FlatZinc;

enum VAR_TYPE  {
    VAR_BOOL,
    VAR_INT,
    VAR_FLOAT,
    VAR_SET_OF_VAR
};

struct PGLNSInfo {
    unsigned long int lnsIndex;
    int domainDiff;
};

// Structs mainly used for CIG LNS.
struct CIGInfo {
    std::vector<double> bound_differences;
    std::vector<double> scores;
    double bound_diff_sum;
    double r;

    explicit CIGInfo(int num_vars) : bound_differences(num_vars), scores(num_vars), bound_diff_sum(0), r(0) {}
};

class LNSstrategies {
public:
    LNSstrategies() = default; // constructor
    ~LNSstrategies() = default; // destructor

    // Standard LNS
    static bool random(FlatZincSpace& fzs, const MetaInfo& mi);
    // Propagation guided LNS
    static bool propagationGuided(FlatZincSpace& fzs, const MetaInfo& mi, unsigned int queue_size);
    // Reversed propagation guided LNS
    static bool reversedPropagationGuided(FlatZincSpace& fzs, const MetaInfo& mi, unsigned int queue_size);
    // Objective relaxation LNS
    static bool objectiveRelaxation(FlatZincSpace& fzs, const MetaInfo& mi);
    // Cost impact guided LNS
    bool costImpactGuided(FlatZincSpace& fzs, const MetaInfo& mi, unsigned int dives, double alpha);
    // Static Variable Dependency LNS
    bool staticVariableRelation(FlatZincSpace& fzs, const MetaInfo& mi);

};

#endif // LNSSTRATEGIES_HH