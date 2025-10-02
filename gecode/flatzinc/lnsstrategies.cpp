// Includes
#include <iostream>
#include <fstream>
#include <gecode/flatzinc.hh>
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

const BoolVar& lnsBoolVarConst(const FlatZincSpace& fzs, int index) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[index];
}

const BoolVar& lnsBoolVarConst(const FlatZincSpace& fzs, int index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[(*iv_indices)[index]];
}

BoolVar& lnsBoolVar(FlatZincSpace& fzs, int index) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[index];
}

BoolVar& lnsBoolVar(FlatZincSpace& fzs, int index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.bv_lns[index] : fzs.bv[(*iv_indices)[index]];
}

void freezeBool(FlatZincSpace& fzs, const FlatZincSpace& last, int index) {
  rel(fzs, lnsBoolVar(fzs, index), IRT_EQ, lnsBoolVarConst(last, index).val());
}

void freezeBool(FlatZincSpace& fzs, const FlatZincSpace& last, int index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  rel(fzs, lnsBoolVar(fzs, index, iv_indices), IRT_EQ, lnsBoolVarConst(last, index, iv_indices).val());
}

const IntVar& lnsIntVarConst(const FlatZincSpace& fzs, int index) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[index];
}

const IntVar& lnsIntVarConst(const FlatZincSpace& fzs, int index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[(*iv_indices)[index]];
}

IntVar& lnsIntVar(FlatZincSpace& fzs, int index) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[index];
}

IntVar& lnsIntVar(FlatZincSpace& fzs, int index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
  return fzs.hasLnsVars() ? fzs.iv_lns[index] : fzs.iv[(*iv_indices)[index]];
}

void freezeInt(FlatZincSpace& fzs, const FlatZincSpace& last, int index) {
  rel(fzs, lnsIntVar(fzs, index), IRT_EQ, lnsIntVarConst(last, index).val());
}

void freezeInt(FlatZincSpace& fzs, const FlatZincSpace& last, int index, const std::shared_ptr<const std::vector<int>>& iv_indices) {
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

int typeToInt(VAR_TYPE t) {
  switch (t) {
    case VAR_BOOL:
      return 0;
    case VAR_INT:
      return 1;
    case VAR_FLOAT:
      return 2;
    case VAR_SET_OF_VAR:
      return 3;
  }
  return -1;
}

VAR_TYPE intToType(int t) {
  switch (t) {
    case 0:
      return VAR_BOOL;
    case 1:
      return VAR_INT;
    case 2:
      return VAR_FLOAT;
    case 3:
      return VAR_SET_OF_VAR;
    default:
      return VAR_INT;
  }
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

  const auto lnsVars = createLnsVars(fzs);

  for (const auto& lnsVar : lnsVars) {
    if (fzs.random()(99U) <= fzs.freezePercent()) {
      freeze(fzs, *last, lnsVar);
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
    const unsigned int indexFreezeVar = indices[index_pos];
    std::swap(indices[index_pos], indices.back());
    indices.pop_back();
    if (!queue.empty()) {
      inQueue[queue.front()] = false;
      queue.pop_front();
    }
    if (isAssigned(fzs, lnsVars[indexFreezeVar])) {
      continue;
    }
    // Get the domain size before the propagation
    for (unsigned int lnsIndex : indices) {
      assert(indexFreezeVar != lnsIndex);
      domainDifferences[lnsIndex] = static_cast<int>(domainSize(fzs, lnsVars[lnsIndex]));
    }
    // Force value accordingly, and propagate.
    freeze(fzs, *last, lnsVars[indexFreezeVar]);
    ++vars_frozen;
    fzs.status();

    // Add the variables that were propagated to pglns_info.
    for (unsigned int lnsIndex : indices) {
      domainDifferences[lnsIndex] -= static_cast<int>(domainSize(fzs, lnsVars[lnsIndex]));
      assert(indexFreezeVar != lnsIndex);
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

  const auto lnsVars = createLnsVars(fzs);
  int limit = floor(static_cast<double>(lnsVars.size()) * (static_cast<double>(fzs.freezePercent()) / 100.0));
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
    const unsigned int indexFreezeVar = indices[index_pos];

    std::swap(indices[index_pos], indices.back());
    indices.pop_back();
    if (!queue.empty()) {
      inQueue[queue.front()] = false;
      queue.pop_front();
    }
    if (isAssigned(fzs, lnsVars[indexFreezeVar])) {
      continue;
    }
    // Get the domain size before the propagation
    for (const unsigned int lnsIndex : indices) {
      domainDifferences[lnsIndex] = static_cast<int>(domainSize(fzs, lnsVars[lnsIndex]));
    }
    // Force value accordingly, and propagate.
    freeze(fzs, *last, lnsVars[indexFreezeVar]);
    vars_frozen++;
    fzs.status();

    // Add the variables that were propagated to the queue.
    for (const unsigned int lnsIndex : indices) {
      domainDifferences[lnsIndex] -= static_cast<int>(domainSize(fzs, lnsVars[lnsIndex]));
      // avg_propagation /= indices.size();
      if (!inQueue[lnsIndex] && domainDifferences[lnsIndex] > 0 && queue.size() < queue_size && !isAssigned(fzs, lnsVars[lnsIndex])) {
        queue.emplace_back(lnsIndex);
        inQueue[lnsIndex] = true;
      }
    }

    // Sort the variables and indexes in non_fzn_introduced_vars according to the difference in domain size in pglns_info.
    std::sort(queue.begin(), queue.end(), [&domainDifferences](const unsigned int& i1, const unsigned int& i2) {
      return domainDifferences[i1] < domainDifferences[i2];
    });
  }
  return false;
}

bool LNSstrategies::objectiveRelaxation(FlatZincSpace& fzs, const MetaInfo& mi){
  if (fzs.default_iv_obj_relax_indices == nullptr || fzs.default_iv_obj_relax_indices->empty()) {
    return random(fzs, mi);
  }
  if (!shouldPerformLns(fzs, mi)) {
    return true;
  }
  const auto last = getLast(fzs, mi);
  if (last == nullptr) {
    return true;
  }
  updateLastBest(fzs, mi, *last);


  for (const int intVarIndex : *(fzs.default_iv_obj_relax_indices)) {
    if (fzs.random()(99U) <= fzs.freezePercent()) {
      rel(fzs, fzs.iv[intVarIndex], IRT_EQ, last->iv[intVarIndex].val());
    }
  }
  return false;
}

int getBound(const BoolVar& var, bool minimize) {
  return minimize ? var.min() : var.max();
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
  const auto lnsVars = createLnsVars(fzs);
  std::vector<int> indices(lnsVars.size());
  std::iota(indices.begin(), indices.end(), 0);

  // Note that we are constructing the set of variables that are relaxed, not frozen.

  // Update scores and r every 10th restart or every time a better solution is found.
  if (fzs.ciglns_info == nullptr || fzs.ciglns_info->bound_differences.empty() || mi.restart() % 10 == 0 || foundBetter){
    if (fzs.ciglns_info == nullptr) {
      fzs.ciglns_info = std::make_shared<CIGInfo>(0);
    }
    fzs.ciglns_info->bound_differences.clear();
    fzs.ciglns_info->bound_differences.resize(lnsVars.size(), 0.0);
    fzs.ciglns_info->scores.clear();
    fzs.ciglns_info->scores.resize(lnsVars.size());
    fzs.ciglns_info->bound_diff_sum = 0.0;
    fzs.ciglns_info->r = 0.0;
    
    for (unsigned int dive = 0; dive < dives; dive++){
      // Clone the space to make a dive possible.
      auto* fzs_clone = dynamic_cast<FlatZinc::FlatZincSpace*>(fzs.clone());
      // Create uniformly randomized permutations of the variables.
      
      // Depending on opt method, calculate the bound differences after fixing the variables.
      for (int i = 0; i < static_cast<int>(lnsVars.size()); ++i){
        std::swap(indices[i], indices[randInInterval(i, static_cast<int>(indices.size()), fzs.random())]);

        const int oldBound = getBound(fzs_clone->iv[fzs_clone->optVar()], fzs.method() == FlatZincSpace::MIN);
        // The variables stored in vars.intVar are those variables found in iv_lns_default.
        const int lnsFreezeVar = indices[i];
        freeze(*fzs_clone, *last, lnsVars[lnsFreezeVar]);
        fzs_clone->status();

        const int newBound = getBound(fzs_clone->iv[fzs_clone->optVar()], fzs.method() == FlatZincSpace::MIN);
        // Corresponds to (3) in the paper:
        // if minimising, then newBound >= oldBound. If newBound is high, then impact is high
        // else, maximising and oldBound >= newBound. If newBound is low, then impact is high
        const int impact = std::abs(newBound - oldBound);

        fzs.ciglns_info->bound_differences[lnsFreezeVar] += static_cast<double>(impact);
        fzs.ciglns_info->bound_diff_sum += static_cast<double>(impact);
      }
      delete fzs_clone;
    }
    // Divide each element in bound differences by dives.
    for (size_t i = 0; i < lnsVars.size(); ++i){
      // corresponds to (6) in the paper:
      fzs.ciglns_info->bound_differences[i] /= dives;
    }
    // corresponds to (6) in the paper:
    fzs.ciglns_info->bound_diff_sum /= dives;

    // Compute the score for each variable.
    for (size_t i = 0; i < lnsVars.size(); ++i){
      // corresponds to (7) in the paper:
      const double score = (alpha * fzs.ciglns_info->bound_differences[i]) + 
                           ((1 - alpha) * static_cast<double>(lnsVars.size()) * fzs.ciglns_info->bound_diff_sum);
      fzs.ciglns_info->r += score;
      fzs.ciglns_info->scores[i] = score;
    }
  }

  const double relaxFactor = static_cast<double>(100 - fzs.freezePercent()) / 100.0;
  const size_t numVarsToRelax = std::max<size_t>(1,
    ceil(relaxFactor * static_cast<double>(lnsVars.size())));

  // The following it based on Algorithm 1 from the paper:
  // Select the variables to relax.
  double r_local = fzs.ciglns_info->r;
  size_t numRelaxed = 0;

  for (numRelaxed = 0; !indices.empty() && numRelaxed < numVarsToRelax; ++numRelaxed) {
    double v = r_local <= 0
             ? 0
             : fzs.random()(static_cast<int>(floor(r_local)));
    
    int best_index = -1;
    double best_score = 0;
    for (int i = 0; i < static_cast<int>(indices.size()); ++i) {
      std::swap(indices[i], indices[randInInterval(i, static_cast<int>(indices.size()), fzs.random())]);
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
  for (const int lnsIndex : indices) {
    freeze(fzs, *last, lnsVars[lnsIndex]);
  }
  // Only return false if variables were relaxed.
  return numRelaxed > 0;
}

int selectRandomBestIndex(FlatZincSpace& fzs, std::vector<std::pair<VAR_TYPE, int>>& lnsVars, int n){

  int best_impact = -1;
  int best_index = -1;
  
  for (int i = 0; i < std::min<int>(n, static_cast<int>(lnsVars.size())); ++i) {
    std::swap(lnsVars[i], lnsVars[randInInterval(i, static_cast<int>(lnsVars.size()), fzs.random())]);
    const int type = typeToInt(lnsVars[i].first);
    const int impact = fzs.variable_impacts->at(type).at(lnsVars[i].second);
    if (best_index < 0 || best_impact < impact) {
      best_impact = impact;
      best_index = i;
    }
  }

  return best_index;
}

int selectRandomRelatedIndex(FlatZincSpace& fzs, std::vector<std::pair<VAR_TYPE, int>>& lnsVars, const std::pair<VAR_TYPE, int>& bestLnsVar, int n){
  // Given indices to relations, select variable with the best relations.
  int best_index = -1;
  double best_relation = -1;
  const int type1 = bestLnsVar.first;
  const int index1 = bestLnsVar.second;
  for (int i = 0; i < std::min<int>(n, static_cast<int>(lnsVars.size())); i++){
    std::swap(lnsVars[i], lnsVars[randInInterval(i, static_cast<int>(lnsVars.size()), fzs.random())]);
    const int type2 = typeToInt(lnsVars[i].first);
    const int index2 = lnsVars[i].second;
    if (best_index < 0 || fzs.variable_relations->at(type1).at(index1).at(type2).at(index2) > best_relation) {
      best_relation = fzs.variable_relations->at(type1).at(index1).at(type2).at(index2);
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

  auto lnsVars = createLnsVars(fzs);
  const std::array<int, 4> lnsSizes{
  fzs.hasLnsVars() ? fzs.bv_lns.size() : fzs.bv.size(),
  fzs.hasLnsVars() ? fzs.iv_lns.size() : fzs.iv.size(),
  fzs.hasLnsVars() ? fzs.fv_lns.size() : fzs.fv.size(),
  fzs.hasLnsVars() ? fzs.sv_lns.size() : fzs.sv.size()};

  if (fzs.variable_impacts == nullptr || foundBetter ||
    fzs.variable_impacts->at(0).size() < lnsSizes[0] ||
    fzs.variable_impacts->at(1).size() < lnsSizes[1] ||
    fzs.variable_impacts->at(2).size() < lnsSizes[2] ||
    fzs.variable_impacts->at(3).size() < lnsSizes[3]) {

    if (fzs.variable_impacts == nullptr) {
      fzs.variable_impacts = std::make_shared<std::array<std::vector<int>, 4>>();
    }

    for (int t = 0; t < lnsSizes.size(); ++t) {
      fzs.variable_impacts->at(t).resize(lnsSizes[t]);
    }

    const int oldBound = getBound(last->iv[fzs.optVar()], fzs.method() == FlatZincSpace::MIN);
    for (const auto& lnsVar : lnsVars) {
      auto* fzs_clone = dynamic_cast<FlatZincSpace*>(fzs.clone());

      freeze(*fzs_clone, *last, lnsVar);
      fzs_clone->status();

      const int newBound = getBound(fzs_clone->iv[fzs_clone->optVar()], fzs.method() == FlatZincSpace::MIN);
      const int impact = std::abs(newBound - oldBound);
      fzs.variable_impacts->at(typeToInt(lnsVar.first)).at(lnsVar.second) = impact;
      delete fzs_clone;
    }
  }
  
  const double relaxFactor = static_cast<double>(100 - fzs.freezePercent()) / 100.0;
  const size_t numVarsToRelax = std::max<size_t>(1, static_cast<size_t>(ceil(relaxFactor * static_cast<double>(lnsVars.size()))));
  const int n = 10 - static_cast<int>(round(5.0 * relaxFactor));

  std::pair<VAR_TYPE, int> bestLnsVar = {VAR_BOOL, -1};
  for (int i = 0; i < numVarsToRelax && !lnsVars.empty(); ++i) {
    // Select variable to relax:
    const int best_index = i % 2 == 0
                             ? selectRandomBestIndex(fzs, lnsVars, n)
                             : selectRandomRelatedIndex(fzs, lnsVars, bestLnsVar, n);
    bestLnsVar = lnsVars[best_index];
    // remove best_index from indices
    lnsVars[best_index] = lnsVars.back();
    lnsVars.pop_back();
  }
  // freeze all non-relaxed variables:
  for (const auto& lnsVar : lnsVars) {
    freeze(fzs, *last, lnsVar);
  }

  return false;
}