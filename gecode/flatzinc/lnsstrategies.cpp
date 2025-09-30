// Includes
#include <iostream>
#include <fstream>
#include <gecode/flatzinc.hh>
#include <gecode/flatzinc/plugin.hh>
#include <gecode/flatzinc/branch.hh>
#include <gecode/search.hh>
#include <gecode/flatzinc/fzn-pbs.hh>
#include <gecode/flatzinc/lnsstrategies.hh>

#include <array>
#include <vector>
#include <deque>
#include <string>
#include <sstream>
#include <limits>
#include <unordered_set>
#include <cstdlib> // for rand() and srand()
#include <ctime> // for time()
#include <random>
#include <memory>

using namespace std;
using namespace Gecode;
using namespace Gecode::FlatZinc;

bool hasLast(const FlatZincSpace& fzs, const MetaInfo& mi) {
  return fzs._incumbentSolution->hasValue() || mi.last() != nullptr;
}

std::shared_ptr<const FlatZincSpace> getLast(FlatZincSpace& fzs, const MetaInfo& mi) {
  if (fzs._incumbentSolution != nullptr) {
    auto last = fzs._incumbentSolution->load();
    if (last != nullptr) {
      return last;
    }
  }
  if (mi.last() != nullptr) {
    return std::dynamic_pointer_cast<const FlatZincSpace>(mi.last());
  }
  return nullptr;
}

const BoolVar& lnsBoolVarConst(const FlatZincSpace& fzs, size_t index) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[index];
}

const BoolVar& lnsBoolVarConst(const FlatZincSpace& fzs, size_t index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[(*iv_indices)[index]];
}

BoolVar& lnsBoolVar(FlatZincSpace& fzs, size_t index) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[index];
}

BoolVar& lnsBoolVar(FlatZincSpace& fzs, size_t index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[(*iv_indices)[index]];
}

void freezeBool(FlatZincSpace& fzs, const FlatZincSpace& last, size_t index) {
  rel(fzs, lnsBoolVar(fzs, index), IRT_EQ, lnsBoolVarConst(last, index).val());
}

void freezeBool(FlatZincSpace& fzs, const FlatZincSpace& last, size_t index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  rel(fzs, lnsBoolVar(fzs, index, iv_indices), IRT_EQ, lnsBoolVarConst(last, index, iv_indices).val());
}

const IntVar& lnsIntVarConst(const FlatZincSpace& fzs, size_t index) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[index];
}

const IntVar& lnsIntVarConst(const FlatZincSpace& fzs, size_t index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[(*iv_indices)[index]];
}

IntVar& lnsIntVar(FlatZincSpace& fzs, size_t index) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[index];
}

IntVar& lnsIntVar(FlatZincSpace& fzs, size_t index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[(*iv_indices)[index]];
}

void freezeInt(FlatZincSpace& fzs, const FlatZincSpace& last, size_t index) {
  rel(fzs, lnsIntVar(fzs, index), IRT_EQ, lnsIntVarConst(last, index).val());
}

void freezeInt(FlatZincSpace& fzs, const FlatZincSpace& last, size_t index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  rel(fzs, lnsIntVar(fzs, index, iv_indices), IRT_EQ, lnsIntVarConst(last, index, iv_indices).val());
}

bool shouldPerformLns(const FlatZincSpace& fzs, const MetaInfo& mi) {
  return (mi.type() == MetaInfo::RESTART &&
         (fzs.freezePercent() > 0 && fzs.freezePercent() < 100) &&
         hasLast(fzs, mi));
}

std::vector<std::pair<VAR_TYPE, int>> createLnsVars(const FlatZincSpace& fzs) {
  vector<std::pair<VAR_TYPE, int>> lnsVars;
  lnsVars.reserve(fzs.hasLnsVars() ? fzs.numLnsVars() : fzs.numVars());
  const int numBoolVars = fzs.hasLnsVars() ? fzs.bv_lns.size() : fzs.bv.size();
  for (size_t i = 0; i < numBoolVars; ++i) {
    lnsVars.emplace_back(VAR_BOOL, i);
  }
  const int numIntVars = fzs.hasLnsVars() ? fzs.iv_lns.size() : fzs.iv.size();
  for (size_t i = 0; i < numIntVars; ++i) {
    lnsVars.emplace_back(VAR_INT, i);
  }
  const int numFloatVars = fzs.hasLnsVars() ? fzs.fv_lns.size() : fzs.fv.size();
  for (size_t i = 0; i < numFloatVars; ++i) {
    lnsVars.emplace_back(VAR_FLOAT, i);
  }
  const int numSetVars = fzs.hasLnsVars() ? fzs.sv_lns.size() : fzs.sv.size();
  for (size_t i = 0; i < numSetVars; ++i) {
    lnsVars.emplace_back(VAR_SET_OF_VAR, i);
  }
  return lnsVars;
}

bool isAssigned(const FlatZincSpace& fzs, const std::pair<VAR_TYPE, int>& var_index) {
  switch (var_index.first) {
    case VAR_BOOL:
      return lnsBoolVarConst(fzs, var_index.second).assigned();
    case VAR_INT:
    default:
      return lnsIntVarConst(fzs, var_index.second).assigned();

  }
}

unsigned int domainSize(const FlatZincSpace& fzs, const std::pair<VAR_TYPE, int>& var_index) {
  switch (var_index.first) {
    case VAR_BOOL:
      return lnsBoolVarConst(fzs, var_index.second).size();
    case VAR_INT:
      default:
        return lnsIntVarConst(fzs, var_index.second).size();
  }
}

void freeze(FlatZincSpace& fzs, const FlatZincSpace& last, const std::pair<VAR_TYPE, int>& var_index) {
  switch (var_index.first) {
    case VAR_BOOL:
      return freezeBool(fzs, last, var_index.second);
    case VAR_INT:
    default:
      return freezeInt(fzs, last, var_index.second);
  }
}


bool updateLastBest(FlatZincSpace& fzs, const MetaInfo& mi, const FlatZincSpace& last) {
  const bool minimizing = fzs.method() == FlatZincSpace::MIN;
  const int obj = minimizing
    ? last.iv[fzs.optVar()].min()
    : last.iv[fzs.optVar()].max();
  const bool isBetter = minimizing
    ? obj < *fzs.last_best_objective
    : obj > *fzs.last_best_objective;
  if (isBetter) {
    *fzs.last_best_objective = obj;
    *fzs.last_best_restart = mi.restart();
    return true;
  }
  return false;
}

bool LNSstrategies::random(FlatZincSpace& fzs, const MetaInfo& mi) {
  if (!shouldPerformLns(fzs, mi)) {
    return true;
  }
  const auto last = getLast(fzs, mi);
  if (last == nullptr) {
    return true;
  }
  updateLastBest(fzs, mi, *last);

  const size_t iv_idx_size = fzs.hasLnsVars() ? fzs.iv_lns.size() : fzs.iv.size();

  for (size_t var_index = 0; var_index < iv_idx_size; ++var_index) {
    if (fzs.random()(99U) <= fzs.freezePercent()) {
      freezeInt(fzs, *last, var_index);
    }
  }

  const size_t bv_idx_size = fzs.hasLnsVars() ? fzs.bv_lns.size() : fzs.bv.size();
  for (size_t var_index = 0; var_index < bv_idx_size; ++var_index) {
    if (fzs.random()(99U) <= fzs.freezePercent()) {
      freezeBool(fzs, *last, var_index);
    }
  }

  return false;
}

bool LNSstrategies::propagationGuided(FlatZincSpace& fzs, const MetaInfo& mi, unsigned int queue_size) {
  if (!shouldPerformLns(fzs, mi)) {
    return true;
  }
  const auto last = getLast(fzs, mi);
  if (last == nullptr) {
    return true;
  }
  updateLastBest(fzs, mi, *last);
  const auto lnsVars = createLnsVars(fzs);

  size_t limit = floor(double(lnsVars.size()) * (double(fzs.freezePercent()) / 100.0));
  size_t vars_frozen = 0;
  // Set up the variables for the propagation guided LNS.
  std::deque<unsigned int> queue;
  std::vector<bool> inQueue(lnsVars.size(), false);
  vector<int> domainDifferences(lnsVars.size());
  vector<unsigned int> indices(lnsVars.size());
  std::iota(indices.begin(), indices.end(), 0);



  while (!indices.empty() && (vars_frozen < limit || (indices.size() + vars_frozen < lnsVars.size()))) {
    const unsigned int index_pos = queue.empty()
      ? fzs.random()(static_cast<int>(indices.size()))
      : queue.front();
    const unsigned int index = indices[index_pos];
    std::swap(indices[index_pos], indices.back());
    indices.pop_back();
    if (!queue.empty()) {
      inQueue[queue.front()] = false;
      queue.pop_front();
    }
    if (isAssigned(fzs, lnsVars[index])) {
      continue;
    }
    if (indices.empty()) {
      break;
    }
    // Get the domain size before the propagation
    for (unsigned int lnsIndex : indices) {
      assert(index != lnsIndex);
      domainDifferences[lnsIndex] = static_cast<int>(domainSize(fzs, lnsVars[lnsIndex]));
    }
    // Force value accordingly, and propagate.
    freeze(fzs, *last, lnsVars[index]);
    ++vars_frozen;
    fzs.status();

    // Add the variables that were propagated to pglns_info.
    for (unsigned int lnsIndex : indices) {
      domainDifferences[lnsIndex] -= static_cast<int>(domainSize(fzs, lnsVars[lnsIndex]));
      assert(index != lnsIndex);
      if (!inQueue[lnsIndex] && domainDifferences[lnsIndex] > 0 && queue.size() < queue_size && !isAssigned(fzs, lnsVars[lnsIndex])) {
        queue.push_back(lnsIndex);
        inQueue[lnsIndex] = true;
      }
    }

    // Sort the variables and indices in non_fzn_introduced_vars according to the difference in domain size in pglns_info.
    std::sort(queue.begin(), queue.end(), [&domainDifferences](const unsigned int& i1, const unsigned int& i2) {
      return domainDifferences[i1] > domainDifferences[i2];
    });
  }
  return false;
}

bool LNSstrategies::reversedPropagationGuided(FlatZincSpace& fzs, const MetaInfo& mi, unsigned int queue_size) {
    if (!shouldPerformLns(fzs, mi)) {
      return true;
    }
    const auto last = getLast(fzs, mi);
    if (last == nullptr) {
      return true;
    }
    updateLastBest(fzs, mi, *last);
    // const FlatZincSpace& last = static_cast<const FlatZincSpace&>(*mi.last());
    // Set up the variables to make sure that pglns stops.
    // double test = 0;
    // double stop = test * 0.80;
    size_t idx_size = fzs.hasLnsVars() ? fzs.iv_lns.size() : fzs.iv.size();
    int limit = floor(static_cast<double>(idx_size) * (static_cast<double>(fzs.freezePercent()) / 100.0));
    size_t vars_frozen = 0;
    // Set up the variables for the propagation guided LNS.
    std::deque<PGLNSInfo> pglns_info;
    vector<int> domainSizes(idx_size);
    vector<int> indices(idx_size);
    std::iota(indices.begin(), indices.end(), 0);
    double avg_propagation;

    int index;
    PGLNSInfo pglns_info_elem;

    while (vars_frozen < limit || (indices.size() + vars_frozen < idx_size)) {
      if (indices.empty()) break;
      std::fill(domainSizes.begin(), domainSizes.end(), 0);
      avg_propagation = 0;
      // std::fill(domainSizes.begin(), domainSizes.end(), 0);

      if (pglns_info.empty()){
        index = indices[fzs.random()(static_cast<int>(indices.size()))];
        std::swap(indices[index], indices.back());
        indices.pop_back();
        if (lnsIntVar(fzs, index).assigned()) {
          continue;
        }
      }
      else{
        pglns_info_elem = pglns_info.front();
        index = indices[pglns_info_elem.lnsIndex];
        std::swap(indices[pglns_info_elem.lnsIndex], indices.back());
        indices.pop_back();
        pglns_info.pop_front();
      }
      if (indices.empty()) break;
      // Get the domain size before the propagation
      for (unsigned long int i = 0; i < indices.size(); i++) {
        if (index != indices[i] && lnsIntVar(fzs, indices[i]).assigned()) {
          domainSizes[indices[i]] = lnsIntVar(fzs, indices[i]).size();
        }
      }
      // Force value accordinly, and propagate.
      freezeInt(fzs, *last, index);
      vars_frozen++;
      fzs.status();
      
      // Add the variables that were propagated to pglns_info.
      for (unsigned long int i = 0; i < indices.size(); i++) {
        if (index != indices[i] && !lnsIntVar(fzs, indices[i]).assigned()) {
          int diff = domainSizes[indices[i]] - lnsIntVar(fzs, indices[i]).size();
          domainSizes[indices[i]] = diff;
          avg_propagation += diff;
        }
      }
      // avg_propagation /= indices.size();
      for (unsigned long int i = 0; i < indices.size(); i++){
        if (domainSizes[indices[i]] > 0 && pglns_info.size() < queue_size && index != indices[i] && lnsIntVar(fzs, indices[i]).assigned()){
          pglns_info.push_back({i, domainSizes[indices[i]]});
        }
      }
      
      // Sort the variables and indexes in non_fzn_introduced_vars according to the difference in domain size in pglns_info.
      std::sort(pglns_info.begin(), pglns_info.end(), [](const PGLNSInfo& a, const PGLNSInfo& b) {
        return a.domainDiff < b.domainDiff;
      });
    }
    return false;
}

bool LNSstrategies::objectiveRelaxation(FlatZincSpace& fzs, const MetaInfo& mi){
    if (!shouldPerformLns(fzs, mi)) {
      return true;
    }
    const auto last = getLast(fzs, mi);
    if (last == nullptr) {
      return true;
    }
    updateLastBest(fzs, mi, *last);

    size_t idx_size = fzs.hasLnsVars() ? fzs.iv_lns.size() : fzs.default_iv_obj_relax_indices->size();
    for (size_t i = 0; i < idx_size; i++) {
      if (fzs.random()(99U) <= fzs.freezePercent()) {
        if (!lnsIntVar(fzs, i, fzs.default_iv_obj_relax_indices).assigned()){
          freezeInt(fzs, *last, i, fzs.default_iv_obj_relax_indices);
        }
      }
    }
    return false;
  }

int getBound(const IntVar& var, bool minimize){
  return minimize ? var.min() : var.max();
}

int randInInterval(int lowInc, int upExc, Rnd& random) {
  return lowInc + random(upExc - lowInc);
}

bool LNSstrategies::costImpactGuided(FlatZincSpace& fzs, const MetaInfo& mi, unsigned int dives, double alpha){
  if (!shouldPerformLns(fzs, mi)) {
    return true;
  }
  const auto last = getLast(fzs, mi);
  if (last == nullptr) {
    return true;
  }
  const bool foundBetter = updateLastBest(fzs, mi, *last);

  // Use a vector of indices, select variables from it.
  const size_t size = fzs.hasLnsVars() ? fzs.iv_lns.size() : fzs.iv.size();
  std::vector<int> indices(size);
  std::iota(indices.begin(), indices.end(), 0);

  // Note that we are constructing the set of variables that are relaxed, not frozen.

  std::default_random_engine engine(fzs.random()(999U));
  // Update scores and r every 10th restart or every time a better solution is found.
  if (fzs.ciglns_info == nullptr || fzs.ciglns_info->bound_differences.empty() || mi.restart() % 10 == 0 || foundBetter){
    if (fzs.ciglns_info == nullptr) {
      fzs.ciglns_info = std::make_shared<CIGInfo>(0);
    }
    fzs.ciglns_info->bound_differences.clear();
    fzs.ciglns_info->bound_differences.resize(size, 0.0);
    fzs.ciglns_info->scores.clear();
    fzs.ciglns_info->scores.resize(size);
    fzs.ciglns_info->bound_diff_sum = 0.0;
    fzs.ciglns_info->r = 0.0;
    
    for (unsigned int dive = 0; dive < dives; dive++){
      // Clone the space to make a dive possible.
      FlatZincSpace* fzs_clone = static_cast<FlatZinc::FlatZincSpace*>(fzs.clone());
      // Create uniformly randomized permutations of the variables.
      
      // Depending on opt method, calculate the bound differences after fixing the variables.
      for (size_t i = 0; i < size; ++i){
        std::swap(indices[i], indices[randInInterval(i, size, fzs.random())]);

        const int oldBound = getBound(fzs_clone->iv[fzs_clone->optVar()], fzs.method() == FlatZincSpace::MIN);
        // The variables stored in vars.intVar are those variables found in iv_lns_default.
        const int var_index = indices[i];
        freezeInt(*fzs_clone, *last, var_index);
        fzs_clone->status();
        
        const int newBound = getBound(fzs_clone->iv[fzs_clone->optVar()], fzs.method() == FlatZincSpace::MIN);
        // Corresponds to (3) in the paper:
        // if minimising, then newBound >= oldBound. If newBound is high, then impact is high
        // else, maximising and oldBound >= newBound. If newBound is low, then impact is high
        const int impact = std::abs(newBound - oldBound);

        fzs.ciglns_info->bound_differences[var_index] += static_cast<double>(impact);
        fzs.ciglns_info->bound_diff_sum += static_cast<double>(impact);
      }
      delete fzs_clone;
    }
    // Divide each element in bound differences by dives.
    for (size_t i = 0; i < size; ++i){
      // corresponds to (6) in the paper:
      fzs.ciglns_info->bound_differences[i] /= dives;
    }
    // corresponds to (6) in the paper:
    fzs.ciglns_info->bound_diff_sum /= dives;

    // Compute the score for each variable.
    for (size_t i = 0; i < size; ++i){
      // corresponds to (7) in the paper:
      const double score = (alpha * fzs.ciglns_info->bound_differences[i]) + 
                           ((1 - alpha) * (size) * fzs.ciglns_info->bound_diff_sum);
      fzs.ciglns_info->r += score;
      fzs.ciglns_info->scores[i] = score;
    }
  }

  const double relaxFactor = static_cast<double>(100 - fzs.freezePercent()) / 100.0;
  const size_t numVarsToRelax = static_cast<size_t>(std::max<size_t>(1, 
    ceil(relaxFactor * static_cast<double>(size))));

  // The following it based on Algorithm 1 from the paper:
  // Select the variables to relax.
  double r_local = fzs.ciglns_info->r;
  size_t numRelaxed = 0;

  for (numRelaxed = 0; indices.empty() || numRelaxed < numVarsToRelax; ++numRelaxed) {
    double v = r_local <= 0
             ? 0
             : fzs.random()(static_cast<int>(floor(r_local)));
    
    int best_index = -1;
    double best_score = 0;
    for (int i = 0; i < indices.size(); ++i){
      std::swap(indices[i], indices[randInInterval(i, size, fzs.random())]);
      const double score = fzs.ciglns_info->scores[indices[i]];
      v -= score;
      if (v <= 0 || best_index < 0 || best_score < score) {
        best_index = i;
        best_score = score;
        if (v <= 0) {
          break;
        }
      }
    }
    r_local -= best_score;
    // More efficient than erasing the element, because vectors.
    std::swap(indices[best_index], indices.back());
    indices.pop_back();
  }
  
  // freeze the chosen variables.
  for (const int var_index : indices) {
    freezeInt(fzs, *last, var_index);
  }
  // Only return false if variables were relaxed.
  return numRelaxed > 0;

}

int selectRandomBestIndex(FlatZincSpace& fzs, std::vector<int>& indices, int n){

  int best_impact = -1;
  int best_index = -1;
  
  for (size_t i = 0; i < std::min<int>(n, indices.size()); ++i) {
    std::swap(indices[i], indices[randInInterval(i, indices.size(), fzs.random())]);
    const int impact = (*fzs.variable_impacts)[indices[i]];
    if (best_index < 0 || best_impact < impact) {
      best_impact = impact;
      best_index = i;
    }
  }

  return best_index;
}

int selectRandomRelatedIndex(FlatZincSpace& fzs, int lns_index, std::vector<int>& indices, int n){
  // Given indices to relations, select variable with best relations.
  int best_index = -1;
  double best_relation = -1;
  for (int i = 0; i < std::min<int>(n, indices.size()); i++){
    std::swap(indices[i], indices[randInInterval(i, indices.size(), fzs.random())]);
    if (best_index < 0 || (*fzs.variable_relations)[lns_index][indices[i]] > best_relation){
      best_relation = (*fzs.variable_relations)[lns_index][indices[i]];
      best_index = i;
    }
  }

  return best_index;
}

bool LNSstrategies::staticVariableRelation(FlatZincSpace& fzs, const MetaInfo& mi) {
  if (!shouldPerformLns(fzs, mi)) {
    return true;
  }
  const auto last = getLast(fzs, mi);
  if (last == nullptr) {
    return true;
  }
  const bool foundBetter = updateLastBest(fzs, mi, *last);

  const size_t idx_size = fzs.hasLnsVars() ? fzs.iv_lns.size() : fzs.iv.size();

  if (fzs.variable_impacts == nullptr || fzs.variable_impacts->empty() || foundBetter) {
    
    if (fzs.variable_impacts == nullptr) {
      fzs.variable_impacts = std::make_shared<std::vector<int>>();
    }
    fzs.variable_impacts->resize(idx_size);
    const int oldBound = getBound(last->iv[fzs.optVar()], fzs.method() == FlatZincSpace::MIN);
    
    for (size_t var_index = 0; var_index < idx_size; ++var_index){
      FlatZincSpace* fzs_clone = static_cast<FlatZinc::FlatZincSpace*>(fzs.clone());

      freezeInt(*fzs_clone, *last, var_index);
      fzs_clone->status();
      
      const int newBound = getBound(fzs_clone->iv[fzs_clone->optVar()], fzs.method() == FlatZincSpace::MIN);
      const int impact = std::abs(newBound - oldBound);
      (*fzs.variable_impacts)[var_index] = impact;
      delete fzs_clone;
    }
  }
  
  std::vector<int> indices(idx_size);
  std::iota(indices.begin(), indices.end(), 0);
  
  const double relaxFactor = static_cast<double>(100 - fzs.freezePercent()) / 100.0;
  const size_t numVarsToRelax = std::max<size_t>(1, static_cast<size_t>(ceil(relaxFactor * static_cast<double>(idx_size))));
  const int n = 10 - static_cast<int>(round(5.0 * relaxFactor));

  int lns_index = -1;
  for (int i = 0; i < numVarsToRelax && !indices.empty(); ++i) {
    // Select variable to relax:
    int best_index = i % 2 == 0
      ? selectRandomBestIndex(fzs, indices, n)
      : selectRandomRelatedIndex(fzs, lns_index, indices, n);
    lns_index = indices[best_index];
    // remove best_index from indices
    indices[best_index] = indices.back();
    indices.pop_back();
  }
  // freeze all non-relaxed variables:
  for (const int index : indices) {
    freezeInt(fzs, *last, index);
  }

  return false;
}