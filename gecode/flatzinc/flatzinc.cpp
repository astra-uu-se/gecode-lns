/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Guido Tack <tack@gecode.org>
 *
 *  Contributing authors:
 *     Gabriel Hjort Blindell <gabriel.hjort.blindell@gmail.com>
 *
 *  Copyright:
 *     Guido Tack, 2007-2012
 *     Gabriel Hjort Blindell, 2012
 *
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

#include <gecode/flatzinc.hh>
#include <gecode/flatzinc/registry.hh>
#include <gecode/flatzinc/plugin.hh>
#include <gecode/flatzinc/branch.hh>
#include <gecode/flatzinc/fzn-pbs.hh>
#include <gecode/flatzinc/branchmodifier.hh>

#include <gecode/search.hh>

#include <vector>
#include <string>
#include <sstream>
#include <limits>
#include <unordered_set>
#include <numeric>
#include <cmath>
#include <algorithm>
#include <unordered_map>

#include "test/test.hh"


namespace std {

  /// Hashing for tuple sets
  template<> struct hash<Gecode::TupleSet> {
    /// Return hash key for \a x
    forceinline size_t
    operator()(const Gecode::TupleSet& x) const {
      return x.hash();
    }
  };

  /// Hashing for tuple sets
  template<> struct hash<Gecode::SharedArray<int> > {
    /// Return hash key for \a x
    forceinline size_t
    operator()(const Gecode::SharedArray<int>& x) const {
      size_t seed = static_cast<size_t>(x.size());
      for (int i=x.size(); i--; )
        Gecode::cmb_hash(seed, x[i]);
      return seed;
    }
  };

  /// Hashing for DFAs
  template<> struct hash<Gecode::DFA> {
    /// Return hash key for \a d
    forceinline size_t operator()(const Gecode::DFA& d) const {
      return d.hash();
    }
  };

}

namespace Gecode { namespace FlatZinc {

  // Default random number generator
  Rnd defrnd(0);

  /**
   * \brief Branching on the introduced variables
   *
   * This brancher makes sure that when a solution is found for the model
   * variables, all introduced variables are either assigned, or the solution
   * can be extended to a solution of the introduced variables.
   *
   * The advantage over simply branching over the introduced variables is that
   * only one such extension will be searched for, instead of enumerating all
   * possible (equivalent) extensions.
   *
   */
  class AuxVarBrancher : public Brancher {
  protected:
    /// Flag whether brancher is done
    bool done;
    /// Construct brancher
    AuxVarBrancher(Home home, TieBreak<IntVarBranch> int_varsel0,
                   IntValBranch int_valsel0,
                   TieBreak<BoolVarBranch> bool_varsel0,
                   BoolValBranch bool_valsel0
#ifdef GECODE_HAS_SET_VARS
                   ,
                   SetVarBranch set_varsel0,
                   SetValBranch set_valsel0
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                   ,
                   TieBreak<FloatVarBranch> float_varsel0,
                   FloatValBranch float_valsel0
#endif
                   )
      : Brancher(home), done(false),
        int_varsel(int_varsel0), int_valsel(int_valsel0),
        bool_varsel(bool_varsel0), bool_valsel(bool_valsel0)
#ifdef GECODE_HAS_SET_VARS
        , set_varsel(set_varsel0), set_valsel(set_valsel0)
#endif
#ifdef GECODE_HAS_FLOAT_VARS
        , float_varsel(float_varsel0), float_valsel(float_valsel0)
#endif
        {}
    /// Copy constructor
    AuxVarBrancher(Space& home, AuxVarBrancher& b)
      : Brancher(home, b), done(b.done) {}

    /// %Choice that only signals failure or success
    class Choice : public Gecode::Choice {
    public:
      /// Whether brancher should fail
      bool fail;
      /// Initialize choice for brancher \a b
      Choice(const Brancher& b, bool fail0)
        : Gecode::Choice(b,1), fail(fail0) {}
      /// Report size occupied
      virtual size_t size(void) const {
        return sizeof(Choice);
      }
      /// Archive into \a e
      virtual void archive(Archive& e) const {
        Gecode::Choice::archive(e);
        e.put(fail);
      }
    };

    TieBreak<IntVarBranch> int_varsel;
    IntValBranch int_valsel;
    TieBreak<BoolVarBranch> bool_varsel;
    BoolValBranch bool_valsel;
#ifdef GECODE_HAS_SET_VARS
    SetVarBranch set_varsel;
    SetValBranch set_valsel;
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    TieBreak<FloatVarBranch> float_varsel;
    FloatValBranch float_valsel;
#endif

  public:
    /// Check status of brancher, return true if alternatives left.
    virtual bool status(const Space& _home) const {
      if (done) return false;
      const auto& home = dynamic_cast<const FlatZincSpace&>(_home);
      for (int i=0; i<home.iv_aux.size(); i++)
        if (!home.iv_aux[i].assigned()) return true;
      for (int i=0; i<home.bv_aux.size(); i++)
        if (!home.bv_aux[i].assigned()) return true;
#ifdef GECODE_HAS_SET_VARS
      for (int i=0; i<home.sv_aux.size(); i++)
        if (!home.sv_aux[i].assigned()) return true;
#endif
#ifdef GECODE_HAS_FLOAT_VARS
      for (int i=0; i<home.fv_aux.size(); i++)
        if (!home.fv_aux[i].assigned()) return true;
#endif
      // No non-assigned variables left
      return false;
    }
    /// Return choice
    virtual Choice* choice(Space& home) {
      done = true;
      FlatZincSpace& fzs = static_cast<FlatZincSpace&>(*home.clone());
      fzs.needAuxVars = false;
      branch(fzs,fzs.iv_aux,int_varsel,int_valsel);
      branch(fzs,fzs.bv_aux,bool_varsel,bool_valsel);
#ifdef GECODE_HAS_SET_VARS
      branch(fzs,fzs.sv_aux,set_varsel,set_valsel);
#endif
#ifdef GECODE_HAS_FLOAT_VARS
      branch(fzs,fzs.fv_aux,float_varsel,float_valsel);
#endif
      Search::Options opt; opt.clone = false;
      FlatZincSpace* sol = dfs(&fzs, opt);
      if (sol) {
        delete sol;
        return new Choice(*this,false);
      } else {
        return new Choice(*this,true);
      }
    }
    /// Return choice
    virtual Choice* choice(const Space&, Archive& e) {
      bool fail; e >> fail;
      return new Choice(*this, fail);
    }
    /// Perform commit for choice \a c
    virtual ExecStatus commit(Space&, const Gecode::Choice& c, unsigned int) {
      return dynamic_cast<const Choice&>(c).fail ? ES_FAILED : ES_OK;
    }
    /// Print explanation
    virtual void print(const Space&, const Gecode::Choice& c,
                       unsigned int,
                       std::ostream& o) const {
      o << "FlatZinc("
        << (dynamic_cast<const Choice&>(c).fail ? "fail" : "ok")
        << ")";
    }
    /// Copy brancher
    virtual Actor* copy(Space& home) {
      return new (home) AuxVarBrancher(home, *this);
    }
    /// Post brancher
    static void post(Home home,
                     TieBreak<IntVarBranch> int_varsel,
                     IntValBranch int_valsel,
                     TieBreak<BoolVarBranch> bool_varsel,
                     BoolValBranch bool_valsel
#ifdef GECODE_HAS_SET_VARS
                     ,
                     SetVarBranch set_varsel,
                     SetValBranch set_valsel
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                     ,
                     TieBreak<FloatVarBranch> float_varsel,
                     FloatValBranch float_valsel
#endif
                   ) {
      (void) new (home) AuxVarBrancher(home, int_varsel, int_valsel,
                                       bool_varsel, bool_valsel
#ifdef GECODE_HAS_SET_VARS
                                       , set_varsel, set_valsel
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                                       , float_varsel, float_valsel
#endif
                                       );
    }
    /// Delete brancher and return its size
    virtual size_t dispose(Space&) {
      return sizeof(*this);
    }
  };

  class BranchInformationO : public SharedHandle::Object {
  private:
    struct BI {
      std::string r0;
      std::string r1;
      std::vector<std::string> n;
      BI(void) : r0(""), r1(""), n(0) {}
      BI(const std::string& r00, const std::string& r10,
         const std::vector<std::string>& n0)
        : r0(r00), r1(r10), n(n0) {}
    };
    std::vector<BI> v;
    BranchInformationO(std::vector<BI> v0) : v(v0) {}
  public:
    BranchInformationO(void) {}
    virtual ~BranchInformationO(void) {}
    virtual SharedHandle::Object* copy(void) const {
      return new BranchInformationO(v);
    }
    /// Add new brancher information
    void add(BrancherGroup bg,
             const std::string& rel0,
             const std::string& rel1,
             const std::vector<std::string>& n) {
      v.resize(std::max(static_cast<unsigned int>(v.size()),bg.id()+1));
      v[bg.id()] = BI(rel0,rel1,n);
    }
    /// Output branch information
    void print(const Brancher& b,
               unsigned int a, int i, int n, std::ostream& o) const {
      const BI& bi = v[b.group().id()];
      o << bi.n[i] << " " << (a==0 ? bi.r0 : bi.r1) << " " << n;
    }
#ifdef GECODE_HAS_FLOAT_VARS
    void print(const Brancher& b,
               unsigned int a, int i, const FloatNumBranch& nl,
               std::ostream& o) const {
      const BI& bi = v[b.group().id()];
      o << bi.n[i] << " "
        << (((a == 0) == nl.l) ? "<=" : ">=") << nl.n;
    }
#endif
  };

  BranchInformation::BranchInformation(void)
    : SharedHandle(nullptr) {}

  BranchInformation::BranchInformation(const BranchInformation& bi)
    : SharedHandle(bi) {}

  void
  BranchInformation::init(void) {
    assert(object() == nullptr);
    object(new BranchInformationO());
  }

  void
  BranchInformation::add(BrancherGroup bg,
                         const std::string& rel0,
                         const std::string& rel1,
                         const std::vector<std::string>& n) {
    static_cast<BranchInformationO*>(object())->add(bg,rel0,rel1,n);
  }
  void
  BranchInformation::print(const Brancher& b, unsigned int a, int i,
                           int n, std::ostream& o) const {
    dynamic_cast<const BranchInformationO*>(object())->print(b,a,i,n,o);
  }
#ifdef GECODE_HAS_FLOAT_VARS
  void
  BranchInformation::print(const Brancher& b, unsigned int a, int i,
                           const FloatNumBranch& nl, std::ostream& o) const {
    dynamic_cast<const BranchInformationO*>(object())->print(b,a,i,nl,o);
  }
#endif
  template<class Var>
  void varValPrint(const Space &home, const Brancher& b,
                   unsigned int a,
                   Var, int i, const int& n,
                   std::ostream& o) {
    dynamic_cast<const FlatZincSpace&>(home).branchInfo.print(b,a,i,n,o);
  }

#ifdef GECODE_HAS_FLOAT_VARS
  void varValPrintF(const Space &home, const Brancher& b,
                    unsigned int a,
                    FloatVar, int i, const FloatNumBranch& nl,
                    std::ostream& o) {
    dynamic_cast<const FlatZincSpace&>(home).branchInfo.print(b,a,i,nl,o);
  }
#endif

  IntSet vs2is(IntVarSpec* vs) {
    if (vs->assigned) {
      return IntSet(vs->i,vs->i);
    }
    if (vs->domain()) {
      AST::SetLit* sl = vs->domain.some();
      if (sl->interval) {
        return IntSet(sl->min, sl->max);
      } else {
        int* newdom = heap.alloc<int>(static_cast<unsigned long int>(sl->s.size()));
        for (int i=sl->s.size(); i--;)
          newdom[i] = sl->s[i];
        IntSet ret(newdom, sl->s.size());
        heap.free(newdom, static_cast<unsigned long int>(sl->s.size()));
        return ret;
      }
    }
    return IntSet(Int::Limits::min, Int::Limits::max);
  }

  int vs2bsl(BoolVarSpec* bs) {
    if (bs->assigned) {
      return bs->i;
    }
    if (bs->domain()) {
      AST::SetLit* sl = bs->domain.some();
      assert(sl->interval);
      return std::min(1, std::max(0, sl->min));
    }
    return 0;
  }

  int vs2bsh(BoolVarSpec* bs) {
    if (bs->assigned) {
      return bs->i;
    }
    if (bs->domain()) {
      AST::SetLit* sl = bs->domain.some();
      assert(sl->interval);
      return std::max(0, std::min(1, sl->max));
    }
    return 1;
  }

  TieBreak<IntVarBranch>  ann2ivarsel(AST::Node* ann, Rnd rnd, double decay, BranchModifier& bm) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingIntVar(s->id, rnd, decay);
      }
      if (s->id == "input_order")
        return TieBreak<IntVarBranch>(INT_VAR_NONE());
      if (s->id == "first_fail")
        return TieBreak<IntVarBranch>(INT_VAR_SIZE_MIN());
      if (s->id == "anti_first_fail")
        return TieBreak<IntVarBranch>(INT_VAR_SIZE_MAX());
      if (s->id == "smallest")
        return TieBreak<IntVarBranch>(INT_VAR_MIN_MIN());
      if (s->id == "largest")
        return TieBreak<IntVarBranch>(INT_VAR_MAX_MAX());
      if (s->id == "occurrence")
        return TieBreak<IntVarBranch>(INT_VAR_DEGREE_MAX());
      if (s->id == "max_regret")
        return TieBreak<IntVarBranch>(INT_VAR_REGRET_MIN_MAX());
      if (s->id == "most_constrained")
        return TieBreak<IntVarBranch>(INT_VAR_SIZE_MIN(),
                                      INT_VAR_DEGREE_MAX());
      if (s->id == "random") {
        return TieBreak<IntVarBranch>(INT_VAR_RND(rnd));
      }
      if (s->id == "dom_w_deg") {
        return TieBreak<IntVarBranch>(INT_VAR_AFC_SIZE_MAX(decay));
      }
      if (s->id == "afc_min")
        return TieBreak<IntVarBranch>(INT_VAR_AFC_MIN(decay));
      if (s->id == "afc_max")
        return TieBreak<IntVarBranch>(INT_VAR_AFC_MAX(decay));
      if (s->id == "afc_size_min")
        return TieBreak<IntVarBranch>(INT_VAR_AFC_SIZE_MIN(decay));
      if (s->id == "afc_size_max") {
        return TieBreak<IntVarBranch>(INT_VAR_AFC_SIZE_MAX(decay));
      }
      if (s->id == "action_min")
        return TieBreak<IntVarBranch>(INT_VAR_ACTION_MIN(decay));
      if (s->id == "action_max")
        return TieBreak<IntVarBranch>(INT_VAR_ACTION_MAX(decay));
      if (s->id == "action_size_min")
        return TieBreak<IntVarBranch>(INT_VAR_ACTION_SIZE_MIN(decay));
      if (s->id == "action_size_max")
        return TieBreak<IntVarBranch>(INT_VAR_ACTION_SIZE_MAX(decay));
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    return TieBreak<IntVarBranch>(INT_VAR_NONE());  
  }

  IntValBranch ann2ivalsel(AST::Node* ann, std::string& r0, std::string& r1, Rnd rnd, BranchModifier& bm) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingIntVal(s->id, r0, r1, rnd);
      }
      if (s->id == "indomain_min") {
        r0 = "="; r1 = "!=";
        return INT_VAL_MIN();
      }
      if (s->id == "indomain_max") {
        r0 = "="; r1 = "!=";
        return INT_VAL_MAX();
      }
      if (s->id == "indomain_median") {
        r0 = "="; r1 = "!=";
        return INT_VAL_MED();
      }
      if (s->id == "indomain_split") {
        r0 = "<="; r1 = ">";
        return INT_VAL_SPLIT_MIN();
      }
      if (s->id == "indomain_reverse_split") {
        r0 = ">"; r1 = "<=";
        return INT_VAL_SPLIT_MAX();
      }
      if (s->id == "indomain_random") {
        r0 = "="; r1 = "!=";
        return INT_VAL_RND(rnd);
      }
      if (s->id == "indomain") {
        r0 = "="; r1 = "=";
        return INT_VALUES_MIN();
      }
      if (s->id == "indomain_middle") {
        std::cerr << "Warning, replacing unsupported annotation "
                  << "indomain_middle with indomain_median" << std::endl;
        r0 = "="; r1 = "!=";
        return INT_VAL_MED();
      }
      if (s->id == "indomain_interval") {
        std::cerr << "Warning, replacing unsupported annotation "
                  << "indomain_interval with indomain_split" << std::endl;
        r0 = "<="; r1 = ">";
        return INT_VAL_SPLIT_MIN();
      }
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    r0 = "="; r1 = "!=";
    return INT_VAL_MIN();
  }

  IntAssign ann2asnivalsel(AST::Node* ann, Rnd rnd) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (s->id == "indomain_min")
        return INT_ASSIGN_MIN();
      if (s->id == "indomain_max")
        return INT_ASSIGN_MAX();
      if (s->id == "indomain_median")
        return INT_ASSIGN_MED();
      if (s->id == "indomain_random") {
        return INT_ASSIGN_RND(rnd);
      }
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    return INT_ASSIGN_MIN();
  }

  TieBreak<BoolVarBranch> ann2bvarsel(AST::Node* ann, Rnd rnd, double decay, BranchModifier& bm) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingBoolVar(s->id, rnd, decay);
      }
      if ((s->id == "input_order") ||
          (s->id == "first_fail") ||
          (s->id == "anti_first_fail") ||
          (s->id == "smallest") ||
          (s->id == "largest") ||
          (s->id == "max_regret"))
      return TieBreak<BoolVarBranch>(BOOL_VAR_NONE());
      if ((s->id == "occurrence") ||
          (s->id == "most_constrained"))
        return TieBreak<BoolVarBranch>(BOOL_VAR_DEGREE_MAX());
      if (s->id == "random")
        return TieBreak<BoolVarBranch>(BOOL_VAR_RND(rnd));
      if ((s->id == "afc_min") ||
          (s->id == "afc_size_min"))
        return TieBreak<BoolVarBranch>(BOOL_VAR_AFC_MIN(decay));
      if ((s->id == "afc_max") ||
          (s->id == "afc_size_max") ||
          (s->id == "dom_w_deg"))
        return TieBreak<BoolVarBranch>(BOOL_VAR_AFC_MAX(decay));
      if ((s->id == "action_min") &&
          (s->id == "action_size_min"))
        return TieBreak<BoolVarBranch>(BOOL_VAR_ACTION_MIN(decay));
      if ((s->id == "action_max") ||
          (s->id == "action_size_max"))
        return TieBreak<BoolVarBranch>(BOOL_VAR_ACTION_MAX(decay));
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    return TieBreak<BoolVarBranch>(BOOL_VAR_NONE());
  }

  BoolValBranch ann2bvalsel(AST::Node* ann, std::string& r0, std::string& r1, Rnd rnd, BranchModifier& bm) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingBoolVal(s->id, r0, r1, rnd);
      }
      if (s->id == "indomain_min") {
        r0 = "="; r1 = "!=";
        return BOOL_VAL_MIN();
      }
      if (s->id == "indomain_max") {
        r0 = "="; r1 = "!=";
        return BOOL_VAL_MAX();
      }
      if (s->id == "indomain_median") {
        r0 = "="; r1 = "!=";
        return BOOL_VAL_MIN();
      }
      if (s->id == "indomain_split") {
        r0 = "<="; r1 = ">";
        return BOOL_VAL_MIN();
      }
      if (s->id == "indomain_reverse_split") {
        r0 = ">"; r1 = "<=";
        return BOOL_VAL_MAX();
      }
      if (s->id == "indomain_random") {
        r0 = "="; r1 = "!=";
        return BOOL_VAL_RND(rnd);
      }
      if (s->id == "indomain") {
        r0 = "="; r1 = "=";
        return BOOL_VAL_MIN();
      }
      if (s->id == "indomain_middle") {
        std::cerr << "Warning, replacing unsupported annotation "
                  << "indomain_middle with indomain_median" << std::endl;
        r0 = "="; r1 = "!=";
        return BOOL_VAL_MIN();
      }
      if (s->id == "indomain_interval") {
        std::cerr << "Warning, replacing unsupported annotation "
                  << "indomain_interval with indomain_split" << std::endl;
        r0 = "<="; r1 = ">";
        return BOOL_VAL_MIN();
      }
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    r0 = "="; r1 = "!=";
    return BOOL_VAL_MIN();
  }

  BoolAssign ann2asnbvalsel(AST::Node* ann, Rnd rnd) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if ((s->id == "indomain_min") ||
          (s->id == "indomain_median"))
        return BOOL_ASSIGN_MIN();
      if (s->id == "indomain_max")
        return BOOL_ASSIGN_MAX();
      if (s->id == "indomain_random") {
        return BOOL_ASSIGN_RND(rnd);
      }
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    return BOOL_ASSIGN_MIN();
  }

#ifdef GECODE_HAS_SET_VARS
  SetVarBranch ann2svarsel(AST::Node* ann, Rnd rnd, double decay, BranchModifier& bm) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingSetVar(s->id, rnd, decay);
      }
      if (s->id == "input_order")
        return SET_VAR_NONE();
      if (s->id == "first_fail")
        return SET_VAR_SIZE_MIN();
      if (s->id == "anti_first_fail")
        return SET_VAR_SIZE_MAX();
      if (s->id == "smallest")
        return SET_VAR_MIN_MIN();
      if (s->id == "largest")
        return SET_VAR_MAX_MAX();
      if (s->id == "afc_min")
        return SET_VAR_AFC_MIN(decay);
      if (s->id == "afc_max")
        return SET_VAR_AFC_MAX(decay);
      if (s->id == "afc_size_min")
        return SET_VAR_AFC_SIZE_MIN(decay);
      if (s->id == "afc_size_max")
        return SET_VAR_AFC_SIZE_MAX(decay);
      if (s->id == "action_min")
        return SET_VAR_ACTION_MIN(decay);
      if (s->id == "action_max")
        return SET_VAR_ACTION_MAX(decay);
      if (s->id == "action_size_min")
        return SET_VAR_ACTION_SIZE_MIN(decay);
      if (s->id == "action_size_max")
        return SET_VAR_ACTION_SIZE_MAX(decay);
      if (s->id == "random") {
        return SET_VAR_RND(rnd);
      }
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    return SET_VAR_NONE();
  }

  SetValBranch ann2svalsel(AST::Node* ann, std::string r0, std::string r1, Rnd rnd, BranchModifier& bm) {
    (void) rnd;
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingSetVal(s->id, r0, r1);
      }
      if (s->id == "indomain_min") {
        r0 = "in"; r1 = "not in";
        return SET_VAL_MIN_INC();
      }
      if (s->id == "indomain_max") {
        r0 = "in"; r1 = "not in";
        return SET_VAL_MAX_INC();
      }
      if (s->id == "outdomain_min") {
        r1 = "in"; r0 = "not in";
        return SET_VAL_MIN_EXC();
      }
      if (s->id == "outdomain_max") {
        r1 = "in"; r0 = "not in";
        return SET_VAL_MAX_EXC();
      }
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    r0 = "in"; r1 = "not in";
    return SET_VAL_MIN_INC();
  }
#endif

#ifdef GECODE_HAS_FLOAT_VARS
  TieBreak<FloatVarBranch> ann2fvarsel(AST::Node* ann, Rnd rnd, double decay, BranchModifier& bm) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingFloatVar(s->id, rnd, decay);
      }
      if (s->id == "input_order")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_NONE());
      if (s->id == "first_fail")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_SIZE_MIN());
      if (s->id == "anti_first_fail")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_SIZE_MAX());
      if (s->id == "smallest")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_MIN_MIN());
      if (s->id == "largest")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_MAX_MAX());
      if (s->id == "occurrence")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_DEGREE_MAX());
      if (s->id == "most_constrained")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_SIZE_MIN(),
                                        FLOAT_VAR_DEGREE_MAX());
      if (s->id == "random") {
        return TieBreak<FloatVarBranch>(FLOAT_VAR_RND(rnd));
      }
      if (s->id == "afc_min")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_AFC_MIN(decay));
      if (s->id == "afc_max")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_AFC_MAX(decay));
      if (s->id == "afc_size_min")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_AFC_SIZE_MIN(decay));
      if (s->id == "afc_size_max")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_AFC_SIZE_MAX(decay));
      if (s->id == "action_min")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_ACTION_MIN(decay));
      if (s->id == "action_max")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_ACTION_MAX(decay));
      if (s->id == "action_size_min")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_ACTION_SIZE_MIN(decay));
      if (s->id == "action_size_max")
        return TieBreak<FloatVarBranch>(FLOAT_VAR_ACTION_SIZE_MAX(decay));
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    return TieBreak<FloatVarBranch>(FLOAT_VAR_NONE());
  }

  FloatValBranch ann2fvalsel(AST::Node* ann, std::string r0, std::string r1, BranchModifier& bm) {
    if (AST::Atom* s = dynamic_cast<AST::Atom*>(ann)) {
      if (bm.do_opposite_branching){
        return bm.doOppositeBranchingFloatVal(s->id, r0, r1);
      }
      if (s->id == "indomain_split") {
        r0 = "<="; r1 = ">";
        return FLOAT_VAL_SPLIT_MIN();
      }
      if (s->id == "indomain_reverse_split") {
        r1 = "<="; r0 = ">";
        return FLOAT_VAL_SPLIT_MAX();
      }
    }
    std::cerr << "Warning, ignored search annotation: ";
    ann->print(std::cerr);
    std::cerr << std::endl;
    r0 = "<="; r1 = ">";
    return FLOAT_VAL_SPLIT_MIN();
  }

#endif

  class FlatZincSpaceInitData {
  public:
    /// Hash table of tuple sets
    typedef std::unordered_set<TupleSet> TupleSetSet;
    /// Hash table of tuple sets
    TupleSetSet tupleSetSet;

    /// Hash table of shared integer arrays
    typedef std::unordered_set<SharedArray<int> > IntSharedArraySet;
    /// Hash table of shared integer arrays
    IntSharedArraySet intSharedArraySet;

    /// Hash table of DFAs
    typedef std::unordered_set<DFA> DFASet;
    /// Hash table of DFAs
    DFASet dfaSet;

    /// Initialize
    FlatZincSpaceInitData(void) {}
  };

  FlatZincSpace::FlatZincSpace(FlatZincSpace& f)
    : Space(f),
      _initData(nullptr), _random(f._random),
      _solveAnnotations(nullptr),
      _assetType(f._assetType),
      _lnsAnnType(f._lnsAnnType),
      _objective_is_sum(f._objective_is_sum),
      default_iv_obj_relax_indices(f.default_iv_obj_relax_indices),
      last_best_restart(f.last_best_restart),
      last_best_objective(f.last_best_objective),
      variable_relations(f.variable_relations),
      variable_impacts(f.variable_impacts),
      ciglns_info(f.ciglns_info),

      restart_data(f.restart_data),
      iv_boolalias(nullptr),
#ifdef GECODE_HAS_FLOAT_VARS
      step(f.step),
#endif
      _incumbentSolution(f._incumbentSolution),
      needAuxVars(f.needAuxVars),
  use_dependency_curated_lns(f.use_dependency_curated_lns),
      _use_soft_subsume(f._use_soft_subsume),
      soften_constraints(f.soften_constraints)
      {
      _optVar = f._optVar;
      _optVarIsInt = f._optVarIsInt;
      _method = f._method;
      _lns = f._lns;
      default_lns = f.default_lns;
      branchInfo = f.branchInfo;
      iv.update(*this, f.iv);

      iv_lns.update(*this, f.iv_lns);

      intVarCount = f.intVarCount;

      on_restart_iv.update(*this, f.on_restart_iv);
      on_restart_bv.update(*this, f.on_restart_bv);
      total_viol.update(*this, f.total_viol);
      viol_vars.reserve(f.viol_vars.size());
      for (int i = 0; i < f.viol_vars.size(); ++i) {
        viol_vars.emplace_back();
        viol_vars.back().update(*this, f.viol_vars[i]);
      }
#ifdef GECODE_HAS_SET_VARS
      on_restart_sv.update(*this, f.on_restart_sv);
#endif
#ifdef GECODE_HAS_FLOAT_VARS
      on_restart_fv.update(*this, f.on_restart_fv);
#endif
      if (needAuxVars) {
        IntVarArgs iva;
        for (int i=0; i<f.iv_aux.size(); i++) {
          if (!f.iv_aux[i].assigned()) {
            iva << IntVar();
            iva[iva.size()-1].update(*this, f.iv_aux[i]);
          }
        }
        iv_aux = IntVarArray(*this, iva);
      }

      bv.update(*this, f.bv);
      boolVarCount = f.boolVarCount;
      if (needAuxVars) {
        BoolVarArgs bva;
        for (int i=0; i<f.bv_aux.size(); i++) {
          if (!f.bv_aux[i].assigned()) {
            bva << BoolVar();
            bva[bva.size()-1].update(*this, f.bv_aux[i]);
          }
        }
        bv_aux = BoolVarArray(*this, bva);
      }
      bv_lns.update(*this, f.bv_lns);

#ifdef GECODE_HAS_SET_VARS
      sv.update(*this, f.sv);
      setVarCount = f.setVarCount;
      if (needAuxVars) {
        SetVarArgs sva;
        for (int i=0; i<f.sv_aux.size(); i++) {
          if (!f.sv_aux[i].assigned()) {
            sva << SetVar();
            sva[sva.size()-1].update(*this, f.sv_aux[i]);
          }
        }
        sv_aux = SetVarArray(*this, sva);
      }
      sv_lns.update(*this, f.sv_lns);
#endif
#ifdef GECODE_HAS_FLOAT_VARS
      fv.update(*this, f.fv);
      floatVarCount = f.floatVarCount;
      if (needAuxVars) {
        FloatVarArgs fva;
        for (int i=0; i<f.fv_aux.size(); i++) {
          if (!f.fv_aux[i].assigned()) {
            fva << FloatVar();
            fva[fva.size()-1].update(*this, f.fv_aux[i]);
          }
        }
        fv_aux = FloatVarArray(*this, fva);
      }
      fv_lns.update(*this, f.fv_lns);
#endif
    }

  FlatZincSpace::FlatZincSpace(Rnd& random)
  : _initData(new FlatZincSpaceInitData),
    intVarCount(-1),
    boolVarCount(-1),
    floatVarCount(-1),
    setVarCount(-1),
    _optVar(-1),
    _optVarIsInt(true),
    _lns(nullptr),
    _random(random),
    _solveAnnotations(nullptr),
    _objective_is_sum(false),
    default_iv_obj_relax_indices(nullptr),
    last_best_restart(nullptr),
    last_best_objective(nullptr),
    variable_relations(nullptr),
    variable_impacts(nullptr),
    ciglns_info(nullptr),
    _lnsAnnType(LNSAnnType::NO_LNS_ANN),
    _incumbentSolution(std::make_shared<IncumbentSolution>()),
    needAuxVars(true),
    use_dependency_curated_lns(true),
    _use_soft_subsume(false),
    soften_constraints(true) {
    branchInfo.init();
  }

  void
  FlatZincSpace::init(int intVars, int boolVars,
                      int setVars, int floatVars) {
    (void) setVars;
    (void) floatVars;

    intVarCount = 0;
    iv = IntVarArray(*this, intVars);
    iv_introduced = std::vector<bool>(2*intVars);
    iv_boolalias = alloc<int>(intVars+(intVars==0?1:0));
    boolVarCount = 0;
    bv = BoolVarArray(*this, boolVars);
    bv_introduced = std::vector<bool>(2*boolVars);

    total_viol = IntVar(*this, 0, Int::Limits::max);
#ifdef GECODE_HAS_SET_VARS
    setVarCount = 0;
    sv = SetVarArray(*this, setVars);
    sv_introduced = std::vector<bool>(2*setVars);
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    floatVarCount = 0;
    fv = FloatVarArray(*this, floatVars);
    fv_introduced = std::vector<bool>(2*floatVars);
#endif
  }

  FlatZincSpace* FlatZincSpace::deepClone() const {
    auto c = dynamic_cast<FlatZincSpace*>(clone());
    // fzs = static_cast<FlatZincSpace*>(fg->copy());
    // Set the solve annotations for the asset, as it does not follow from the clone.
    // Set the shared current best solutions between assets for each asset.
    c->_incumbentSolution = _incumbentSolution;

    // Copy iv,bv,sv_introduced vector from fg, as it does not follow the cloning process.
    c->iv_introduced = iv_introduced;
    c->bv_introduced = bv_introduced;
    c->sv_introduced = sv_introduced;
    c->iv_boolalias = iv_boolalias;
    return c;
  }

  void
  FlatZincSpace::newIntVar(IntVarSpec* vs) {
    if (vs->alias) {
      iv[intVarCount++] = iv[vs->i];
    } else {
      IntSet dom(vs2is(vs));
      if (dom.size()==0) {
        fail();
        return;
      } else {
        iv[intVarCount++] = IntVar(*this, dom);
      }
    }
    iv_introduced[2*(intVarCount-1)] = vs->introduced;
    iv_introduced[2*(intVarCount-1)+1] = vs->funcDep;
    iv_boolalias[intVarCount-1] = -1;
  }

  void
  FlatZincSpace::aliasBool2Int(int iv, int bv) {
    iv_boolalias[iv] = bv;
  }
  int
  FlatZincSpace::aliasBool2Int(int iv) {
    return iv_boolalias[iv];
  }

  void
  FlatZincSpace::newBoolVar(BoolVarSpec* vs) {
    if (vs->alias) {
      bv[boolVarCount++] = bv[vs->i];
    } else {
      bv[boolVarCount++] = BoolVar(*this, vs2bsl(vs), vs2bsh(vs));
    }
    bv_introduced[2*(boolVarCount-1)] = vs->introduced;
    bv_introduced[2*(boolVarCount-1)+1] = vs->funcDep;
  }

#ifdef GECODE_HAS_SET_VARS
  void
  FlatZincSpace::newSetVar(SetVarSpec* vs) {
    if (vs->alias) {
      sv[setVarCount++] = sv[vs->i];
    } else if (vs->assigned) {
      assert(vs->upperBound());
      AST::SetLit* vsv = vs->upperBound.some();
      if (vsv->interval) {
        IntSet d(vsv->min, vsv->max);
        sv[setVarCount++] = SetVar(*this, d, d);
      } else {
        int* is = heap.alloc<int>(static_cast<unsigned long int>(vsv->s.size()));
        for (int i=vsv->s.size(); i--; )
          is[i] = vsv->s[i];
        IntSet d(is, vsv->s.size());
        heap.free(is,static_cast<unsigned long int>(vsv->s.size()));
        sv[setVarCount++] = SetVar(*this, d, d);
      }
    } else if (vs->upperBound()) {
      AST::SetLit* vsv = vs->upperBound.some();
      if (vsv->interval) {
        IntSet d(vsv->min, vsv->max);
        sv[setVarCount++] = SetVar(*this, IntSet::empty, d);
      } else {
        int* is = heap.alloc<int>(static_cast<unsigned long int>(vsv->s.size()));
        for (int i=vsv->s.size(); i--; )
          is[i] = vsv->s[i];
        IntSet d(is, vsv->s.size());
        heap.free(is,static_cast<unsigned long int>(vsv->s.size()));
        sv[setVarCount++] = SetVar(*this, IntSet::empty, d);
      }
    } else {
      sv[setVarCount++] = SetVar(*this, IntSet::empty,
                                 IntSet(Set::Limits::min,
                                        Set::Limits::max));
    }
    sv_introduced[2*(setVarCount-1)] = vs->introduced;
    sv_introduced[2*(setVarCount-1)+1] = vs->funcDep;
  }
#else
  void
  FlatZincSpace::newSetVar(SetVarSpec*) {
    throw FlatZinc::Error("Gecode", "set variables not supported");
  }
#endif

#ifdef GECODE_HAS_FLOAT_VARS
  void
  FlatZincSpace::newFloatVar(FloatVarSpec* vs) {
    if (vs->alias) {
      fv[floatVarCount++] = fv[vs->i];
    } else {
      double dmin, dmax;
      if (vs->domain()) {
        dmin = vs->domain.some().first;
        dmax = vs->domain.some().second;
        if (dmin > dmax) {
          fail();
          return;
        }
      } else {
        dmin = Float::Limits::min;
        dmax = Float::Limits::max;
      }
      fv[floatVarCount++] = FloatVar(*this, dmin, dmax);
    }
    fv_introduced[2*(floatVarCount-1)] = vs->introduced;
    fv_introduced[2*(floatVarCount-1)+1] = vs->funcDep;
  }
#else
  void
  FlatZincSpace::newFloatVar(FloatVarSpec*) {
    throw FlatZinc::Error("Gecode", "float variables not supported");
  }
#endif

  namespace {
    struct ConExprOrder {
      bool operator() (ConExpr* ce0, ConExpr* ce1) {
        if (ce0->ann->hasAtom("soften") == ce1->ann->hasAtom("soften")) {
          return ce0->args->a.size() < ce1->args->a.size();
        }
        return ce0->ann->hasAtom("soften") < ce1->ann->hasAtom("soften");
      }
    };
  }

  void FlatZincSpace::addConstraintInformation(ConExpr* ce){
    if (ce->ann != nullptr && ce->ann->a.size() > 0){
      if ((ce->id == "fzn_all_different_int" && !ce->ann->hasAtom("domain"))){
        // create atom node with id "domain"
        AST::Atom* a = new AST::Atom("domain");
        // append the atom node to ce.ann
        ce->ann->a.push_back(a);
      }
    }
  }

  void FlatZincSpace::postConstraints(std::vector<ConExpr*> constraints, bool addAnnotations){
    // The point of this method is to add be able to add annotations
    // to the constraints before posting them to the space (Domain propagation etc.) for certain assets.
    // Cloning a flatzincspace and posting constraints will not work. Therefore this is put aside for now.

    // for (unsigned int i=0; i<constraints.size(); i++) {
    //   if (addAnnotations){
    //     addConstraintInformation(constraints[i]);
    //   }
    //   const ConExpr& ce = *constraints[i];
    //   try {
    //     registry().post(*this, ce);
    //   } catch (Gecode::Exception& e) {
    //       throw FlatZinc::Error("Gecode", e.what(), ce.ann);
    //   } catch (AST::TypeError& e) {
    //       throw FlatZinc::Error("Type error", e.what(), ce.ann);
    //   }    
    // }
  }

  // Store all the constraints if its an optimization problem. Otherwise, post the constraints to the space.
  void FlatZincSpace::postConstraints(std::vector<ConExpr*>& ces) {
    ConExprOrder ceo;
    std::sort(ces.begin(), ces.end(), ceo);
    constraints.insert(constraints.end(), ces.begin(), ces.end());
    for (unsigned int i=0; i<ces.size(); i++) {
      const ConExpr& ce = *ces[i];
      try {
        registry().post(*this, ce);
      } catch (Gecode::Exception& e) {
          throw FlatZinc::Error("Gecode", e.what(), ce.ann);
      } catch (AST::TypeError& e) {
          throw FlatZinc::Error("Type error", e.what(), ce.ann);
      }
    }
  }

  void flattenAnnotations(AST::Array* ann, std::vector<AST::Node*>& out) {
      for (unsigned int i=0; i<ann->a.size(); i++) {
        if (ann->a[i]->isCall("seq_search")) {
          AST::Call* c = ann->a[i]->getCall();
          if (c->args->isArray())
            flattenAnnotations(c->args->getArray(), out);
          else
            out.push_back(c->args);
        } else {
          out.push_back(ann->a[i]);
        }
      }
  }

  void FlatZincSpace::deletePBSArrays(){
      default_iv_obj_relax_indices = nullptr;
  }

  void FlatZincSpace::populateCostImpactData() {
    ciglns_info = std::make_shared<CIGInfo>(0);
  }

  void FlatZincSpace::populateObjRelData() {
    default_iv_obj_relax_indices = nullptr;
    for (ConExpr* ce : constraints){
      // Ensure that the constraint is of type int_lin_eq and is defined var in compiled fzn file for the use of Objective Relaxation LNS.
      if (ce->id != "int_lin_eq" || ce->ann == nullptr || ce->ann->a.size() == 0 || !ce->ann->getArray()->a[0]->isCall("defines_var")) {
        continue;
      }
      AST::Call* call = ce->ann->getArray()->a[0]->getCall("defines_var");
      AST::Node* var = call->args;

      if (var == nullptr || var->getIntVar() != _optVar) {
        continue;
      }


      AST::Array* coef = ce->args->a[0]->getArray();
      AST::Array* vars = ce->args->a[1]->getArray();

      // Two different cases: All coefficients are similar or some coefficients are larger than others.
      // Loop starts at 1 since the first entry is the objective value itself, and freezing that variable breaks the point of the search.
      const double mean = std::accumulate(coef->a.begin()+1, coef->a.end(), 0.0, [](double acc, AST::Node* b) { return acc + std::abs(b->getInt()); }) / static_cast<double>(coef->a.size()-1);
      const double sq_sum = std::accumulate(coef->a.begin()+1, coef->a.end(), 0.0, [](double sum, AST::Node* b) { int val = b->getInt(); return sum + val * val; });
      const double stdev = std::sqrt((sq_sum / static_cast<double>(coef->a.size()-1)) - (mean * mean));

      // Case 1: coefficients are similar (a standard deviation smaller than 1)
      // Case 2: Some coefficients are larger than other, keep those non-fixed and make those with smaller mean freezeable, to relax the objective.
      default_iv_obj_relax_indices = std::make_shared<std::vector<int>>();
      for (size_t i = 0; i < vars->a.size(); i++) {
        if (vars->a[i]->getIntVar() != _optVar && vars->a[i]->isIntVar() && !iv[vars->a[i]->getIntVar()].assigned() && (stdev < 1 || coef->a[i]->getInt() < mean)) {
          default_iv_obj_relax_indices->emplace_back(vars->a[i]->getIntVar());
        }
      }
    }
  }

  void FlatZincSpace::populateStaticVariableRelationData(const std::vector<ConExpr*>& originalConstraints) {
    std::vector<std::array<std::unordered_set<int>,4>> constraint_input_vars;
    auto addConstraintInput = [&](AST::Node *node) {
      if (node->isBoolVar()) {
        if (!bv[node->getBoolVar()].assigned()) {
          constraint_input_vars.back()[0].emplace(node->getBoolVar());
        }
      } else if (node->isIntVar()) {
        if (!iv[node->getIntVar()].assigned()) {
          constraint_input_vars.back()[1].emplace(node->getIntVar());
        }
      } else if (node->isFloatVar()) {
        if (!fv[node->getFloatVar()].assigned()) {
          constraint_input_vars.back()[2].emplace(node->getFloatVar());
        }
      } else if (node->isSetVar()) {
        if (!fv[node->getFloatVar()].assigned()) {
          constraint_input_vars.back()[3].emplace(node->getSetVar());
        }
      }
    };
    for (const ConExpr* ce : originalConstraints){
      constraint_input_vars.emplace_back();
      for (size_t i = 0; i < ce->args->a.size(); ++i) {
        if (ce->args->a[0]->isArray()) {
          auto arr = ce->args->a[0]->getArray();
          for (const auto & node : arr->a) {
            addConstraintInput(node);
          }
        } else {
          addConstraintInput(ce->args->a[0]);
        }
      }
    }

    // For each variable present, map the iv index to the index that will be used in non_fzn_introduced_vars
    std::unordered_map<BoolVar*, int> bv_lns_indices;
    bv_lns_indices.reserve(useDependencyCuratedLns() ? bv_lns.size() : 0);
    std::unordered_map<IntVar*, int> iv_lns_indices;
    iv_lns_indices.reserve(useDependencyCuratedLns() ? iv_lns.size() : 0);
    std::unordered_map<FloatVar*, int> fv_lns_indices;
    fv_lns_indices.reserve(useDependencyCuratedLns() ? fv_lns.size() : 0);
    std::unordered_map<SetVar*, int> sv_lns_indices;
    sv_lns_indices.reserve(useDependencyCuratedLns() ? sv_lns.size() : 0);

    if (useDependencyCuratedLns()) {
      for (int i = 0;  i < bv_lns.size(); ++i) {
        bv_lns_indices.emplace(&bv_lns[i], i);
      }
      for (int i = 0;  i < iv_lns.size(); ++i) {
        iv_lns_indices.emplace(&iv_lns[i], i);
      }
      for (int i = 0;  i < fv_lns.size(); ++i) {
        fv_lns_indices.emplace(&fv_lns[i], i);
      }
      for (int i = 0;  i < sv_lns.size(); ++i) {
        sv_lns_indices.emplace(&sv_lns[i], i);
      }
    }

    std::vector<int> num_vars(constraint_input_vars.size(), 0);
    for (size_t i = 0; i < constraint_input_vars.size(); i++) {
      for (const int varIndex : constraint_input_vars[i][0]) {
        if (!useDependencyCuratedLns() || bv_lns_indices.find(&bv[varIndex]) != bv_lns_indices.end()) {
          ++num_vars[i];
        }
      }
      for (const int varIndex : constraint_input_vars[i][1]) {
        if (!useDependencyCuratedLns() || iv_lns_indices.find(&iv[varIndex]) != iv_lns_indices.end()) {
          ++num_vars[i];
        }
      }
      for (const int varIndex : constraint_input_vars[i][2]) {
        if (!useDependencyCuratedLns() || fv_lns_indices.find(&fv[varIndex]) != fv_lns_indices.end()) {
          ++num_vars[i];
        }
      }
      for (const int varIndex : constraint_input_vars[i][3]) {
        if (!useDependencyCuratedLns() || sv_lns_indices.find(&sv[varIndex]) != sv_lns_indices.end()) {
          ++num_vars[i];
        }
      }
    }

    std::array<int, 4> lnsVarSizes{
      useDependencyCuratedLns() ? bv_lns.size() : bv.size(),
      useDependencyCuratedLns() ? iv_lns.size() : iv.size(),
      useDependencyCuratedLns() ? fv_lns.size() : fv.size(),
      useDependencyCuratedLns() ? sv_lns.size() : sv.size()
    };

    std::array<std::vector<int>, 4> numConstraints{
      std::vector<int>(lnsVarSizes[0], 0),
      std::vector<int>(lnsVarSizes[1], 0),
      std::vector<int>(lnsVarSizes[2], 0),
      std::vector<int>(lnsVarSizes[3], 0)
    };

    for (const auto & inputData : constraint_input_vars) {
      if (inputData[0].size() + inputData[1].size() + inputData[2].size() + inputData[3].size() <= 1) {
        continue;
      }
      for (const int var_index : inputData[0]) {
        if (useDependencyCuratedLns()) {
          auto* var = &bv[var_index];
          if (bv_lns_indices.find(var) != bv_lns_indices.end()) {
            ++numConstraints[0].at(bv_lns_indices[var]);
          }
        } else {
          ++numConstraints[0].at(var_index);
        }
      }
      for (const int var_index : inputData[1]) {
        if (useDependencyCuratedLns()) {
          auto* var = &iv[var_index];
          if (iv_lns_indices.find(var) != iv_lns_indices.end()) {
            ++numConstraints[1].at(iv_lns_indices[var]);
          }
        } else {
          ++numConstraints[1].at(var_index);
        }
      }
      for (const int var_index : inputData[2]) {
        if (useDependencyCuratedLns()) {
          auto* var = &fv[var_index];
          if (fv_lns_indices.find(var) != fv_lns_indices.end()) {
            ++numConstraints[2].at(fv_lns_indices[var]);
          }
        } else {
          ++numConstraints[2].at(var_index);
        }
      }
      for (const int var_index : inputData[3]) {
        if (useDependencyCuratedLns()) {
          auto* var = &sv[var_index];
          if (sv_lns_indices.find(var) != sv_lns_indices.end()) {
            ++numConstraints[3].at(sv_lns_indices[var]);
          }
        } else {
          ++numConstraints[3].at(var_index);
        }
      }
    }

    auto getIndex = [&](int t, int v) {
      if (!useDependencyCuratedLns()) {
        return v;
      }
      if (t == 0) {
        auto* var = &bv[v];
        if (bv_lns_indices.find(var) == bv_lns_indices.end()) {
          return -1;
        }
        return bv_lns_indices[var];
      }
      if (t == 1) {
        auto* var = &iv[v];
        if (iv_lns_indices.find(var) == iv_lns_indices.end()) {
          return -1;
        }
        return iv_lns_indices[var];
      }
      if (t == 2) {
        auto* var = &fv[v];
        if (fv_lns_indices.find(var) == fv_lns_indices.end()) {
          return -1;
        }
        return fv_lns_indices[var];
      }
      assert(t == 3);
      auto* var = &sv[v];
      if (sv_lns_indices.find(var) == sv_lns_indices.end()) {
        return -1;
      }
      return sv_lns_indices[var];
    };
    variable_relations = std::make_shared<std::array<std::vector<std::array<std::vector<double>,4>>,4>>();
    for (int t1 = 0; t1 < variable_relations->size(); ++t1) {
      variable_relations->at(t1).resize(lnsVarSizes[t1]);
      for (int v1 = 0; v1 < lnsVarSizes[t1]; ++v1) {
        for (int t2 = 0; t2 < variable_relations->size(); ++t2) {
          variable_relations->at(t1).at(v1).at(t2).resize(lnsVarSizes[t2], 0.0);
        }
      }
    }
    auto addRelation = [&](int i, int t1, int v1, int t2, int v2) {
      const int index1 = getIndex(t1, v1);
      const int index2 = getIndex(t2, v2);
      if (index1 >= 0 && index2 >= 0) {
        variable_relations->at(t1).at(index1).at(t2).at(index2) += 1.0 / num_vars[i];
        variable_relations->at(t2).at(index2).at(t1).at(index1) += 1.0 / num_vars[i];
      }
    };
    // The variable_relations matrix is used for Static Variable Dependency LNS asset
    // and contain the relations between the variables given the weights defined for each constraint.
    for (int i = 0; i < static_cast<int>(constraint_input_vars.size()); i++) {
      for (int varType1 = 0; varType1 < 4; ++varType1) {
        for (auto iter1 = constraint_input_vars[i][varType1].begin(); iter1 != constraint_input_vars[i][varType1].end(); ++iter1) {
          auto iter2 = iter1;
          for (++iter2; iter2 != constraint_input_vars[i][varType1].end(); ++iter2){
            addRelation(i, varType1, *iter1, varType1, *iter2);
          }
          for (int varType2 = varType1 + 1; varType2 < 4; ++varType2) {
            for (const int v2 : constraint_input_vars[i][varType2]) {
              addRelation(i, varType1, *iter1, varType2, v2);
            }
          }
        }
      }
    }
    for (int t1 = 0; t1 < 4; ++t1) {
      for (int v1 = 0; v1 < variable_relations->at(t1).size(); ++v1) {
        if (numConstraints[t1][v1] == 0) {
          continue;
        }
        for (int t2 = 0; t2 < 4; ++t2) {
          for (int v2 = 0; v2 < variable_relations->at(t1).at(v1).at(t2).size(); ++v2) {
            variable_relations->at(t1).at(v1).at(t2).at(v2) *= 1.0 / numConstraints[t1][v1];
          }
        }
      }
    }
    variable_impacts = std::make_shared<std::array<std::vector<int>, 4>>();
  }

  void FlatZincSpace::storeConstraintInformation(const std::vector<ConExpr*>& originalConstraints) {
    for (ConExpr* ce : originalConstraints) {
      if (ce->id != "int_lin_eq" || ce->ann == nullptr || ce->ann->a.empty() || !ce->ann->getArray()->a[0]->isCall("defines_var")) {
        continue;
      }
      AST::Call* call = ce->ann->getArray()->a[0]->getCall("defines_var");
      AST::Node* var = call->args;

      if (var != nullptr && var->getIntVar() == _optVar) {
        _objective_is_sum = true;
        break;
      }
    }

    switch (_assetType) {
      case AssetType::CIGLNS:
        populateCostImpactData();
      break;
      case AssetType::SVRLNS:
        populateStaticVariableRelationData(originalConstraints);
      break;
      case AssetType::OBJRELLNS:
        populateObjRelData();
      break;
      default:
        break;
    }
    default_lns = 60;

    last_best_restart = std::make_shared<unsigned long>(0);
    if (last_best_objective == nullptr) {
      last_best_objective = std::make_shared<std::pair<int, int>>(0, 0);
    }
  }

  void
  FlatZincSpace::createBranchers(Printer&p, AST::Node* ann, FlatZincOptions& opt, bool ignoreUnknown, BranchModifier& bm, std::ostream& err) {
    int seed = opt.seed();
    double decay = opt.decay();
    Rnd rnd(static_cast<unsigned int>(seed));
    TieBreak<IntVarBranch> def_int_varsel = bm.def_int_varsel;
    IntBoolVarBranch def_intbool_varsel = INTBOOL_VAR_AFC_SIZE_MAX(0.99);
    IntValBranch def_int_valsel = bm.def_int_valsel;
    std::string def_int_rel_left = "=";
    std::string def_int_rel_right = "!=";
    TieBreak<BoolVarBranch> def_bool_varsel = bm.def_bool_varsel;
    BoolValBranch def_bool_valsel = bm.def_bool_valsel;
    std::string def_bool_rel_left = "=";
    std::string def_bool_rel_right = "!=";
#ifdef GECODE_HAS_SET_VARS
    SetVarBranch def_set_varsel = bm.def_set_varsel;
    SetValBranch def_set_valsel = bm.def_set_valsel;
    std::string def_set_rel_left = "in";
    std::string def_set_rel_right = "not in";
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    TieBreak<FloatVarBranch> def_float_varsel = bm.def_float_varsel;
    FloatValBranch def_float_valsel = bm.def_float_valsel;
    std::string def_float_rel_left = "<=";
    std::string def_float_rel_right = ">";
#endif

    std::vector<bool> iv_searched(iv.size());
    for (unsigned int i=iv.size(); i--;)
      iv_searched[i] = false;
    std::vector<bool> bv_searched(bv.size());
    for (unsigned int i=bv.size(); i--;)
      bv_searched[i] = false;
#ifdef GECODE_HAS_SET_VARS
    std::vector<bool> sv_searched(sv.size());
    for (unsigned int i=sv.size(); i--;)
      sv_searched[i] = false;
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    std::vector<bool> fv_searched(fv.size());
    for (unsigned int i=fv.size(); i--;)
      fv_searched[i] = false;
#endif

    _lns = std::make_shared<unsigned int>(0);
    if (ann || bm.use_pbs_branching) {
      std::vector<AST::Node*> flatAnn;
      // Prioritise PBS branching annotations over annotations by the model, if to use PBS branching.
      if (bm.use_pbs_branching && bm.pbs_variable_branchings){
        AST::Node* bm_ann = bm.pbs_variable_branchings;
        if (bm_ann->isArray()){
          flattenAnnotations(bm_ann->getArray(), flatAnn);
        }
        else{
          flatAnn.push_back(bm_ann);
        }
      }
      if (ann){
        if (ann->isArray()) {
          flattenAnnotations(ann->getArray(), flatAnn);
        } else {
          flatAnn.push_back(ann);
        }
      }

      if (bm.sort_flat_ann){
        bm.sortFlatAnn(flatAnn, iv, bv);
      }

      for (unsigned int i=0; i<flatAnn.size(); i++) {
        if (flatAnn[i]->isCall("restart_geometric")) {
          AST::Call* call = flatAnn[i]->getCall("restart_geometric");
          opt.restart(RM_GEOMETRIC);
          AST::Array* args = call->getArgs(2);
          opt.restart_base(args->a[0]->getFloat());
          opt.restart_scale(args->a[1]->getInt());
        } else if (flatAnn[i]->isCall("restart_luby")) {
          AST::Call* call = flatAnn[i]->getCall("restart_luby");
          opt.restart(RM_LUBY);
          opt.restart_scale(call->args->getInt());
        } else if (flatAnn[i]->isCall("restart_linear")) {
          AST::Call* call = flatAnn[i]->getCall("restart_linear");
          opt.restart(RM_LINEAR);
          opt.restart_scale(call->args->getInt());
        } else if (flatAnn[i]->isCall("restart_constant")) {
          AST::Call* call = flatAnn[i]->getCall("restart_constant");
          opt.restart(RM_CONSTANT);
          opt.restart_scale(call->args->getInt());
        } else if (flatAnn[i]->isCall("restart_none")) {
          opt.restart(RM_NONE);
        } else if (flatAnn[i]->isCall("relax_and_reconstruct")) {
          // Make all LNS assets use the fix percentage given by the modeller
          // Or -1 which will use the fix percentage heuristic defined on line 2744.
          // if (_lnsType != RANDOM){
          //   continue;
          // }
          if (_lnsAnnType != LNSAnnType::NO_LNS_ANN)
            throw FlatZinc::Error("FlatZinc", "Only one relax_and_reconstruct annotation allowed");
          AST::Call *call = flatAnn[i]->getCall("relax_and_reconstruct");
          AST::Array* args;
          if (call->args->getArray()->a.size()==2) {
            args = call->getArgs(2);
          } else {
            args = call->getArgs(3);
          }
          const int freezePercentage = args->a[1]->getInt();
          AST::Array *vars = args->a[0]->getArray();
          int k=vars->a.size();
          for (int i=vars->a.size(); i--;)
            if (vars->a[i]->isInt())
              k--;
          iv_lns = IntVarArray(*this, k);
          k = 0;
          for (unsigned int i=0; i<vars->a.size(); i++) {
            if (vars->a[i]->isInt()) {
              continue;
            }
            iv_lns[k++] = iv[vars->a[i]->getIntVar()];
          }
          if (freezePercentage < 0 || 100 < freezePercentage){
            (*_lns) = default_lns;
            _lnsAnnType = LNSAnnType::ONLY_VARS_ANN;
          } else {
            (*_lns) = freezePercentage;
            _lnsAnnType = LNSAnnType::FULL_LNS_ANN;
          }
        } else if (flatAnn[i]->isCall("warm_start") || flatAnn[i]->isCall("warm_start_array")) {
          continue; // We take care of these annotations elsewhere
        } else if (flatAnn[i]->isCall("gecode_search")) {
          AST::Call* c = flatAnn[i]->getCall();
          branchWithPlugin(c->args);
        } else if (flatAnn[i]->isCall("int_search")) {
          AST::Call *call = flatAnn[i]->getCall("int_search");
          AST::Array *args = call->getArgs(4);
          AST::Array *vars = args->a[0]->getArray();
          int k=vars->a.size();
          for (int i=vars->a.size(); i--;) {
            if (vars->a[i]->isInt() || vars->a[i]->isBool()) {
              k--;
            }
          }
          IntVarArgs va(k);
          std::vector<std::string> names;
          k=0;
          for (unsigned int i=0; i<vars->a.size(); i++) {
            if (vars->a[i]->isInt() || vars->a[i]->isBool()) {
              continue;
            }
            int v_i = -1;
            if (vars->a[i]->isIntVar()) {
              v_i = vars->a[i]->getIntVar();
            } else {
              const int b_i = vars->a[i]->getBoolVar();
              for (int i = 0; i < intVarCount; ++i) {
                if (iv_boolalias[i] == b_i) {
                  v_i = i;
                  break;
                }
              }
            }
            assert(v_i >= 0);
            va[k++] = iv[v_i];
            iv_searched[v_i] = true;
            names.push_back(vars->a[i]->getVarName());
          }
          std::string r0, r1;
          {
            BrancherGroup bg;
            branch(bg(*this), va,
                   ann2ivarsel(args->a[1],rnd,decay, bm),
                   ann2ivalsel(args->a[2],r0,r1,rnd, bm),
                   nullptr,
                   &varValPrint<IntVar>);
            branchInfo.add(bg,r0,r1,names);
          }
        } else if (flatAnn[i]->isCall("int_assign")) {
          AST::Call *call = flatAnn[i]->getCall("int_assign");
          AST::Array *args = call->getArgs(2);
          AST::Array *vars = args->a[0]->getArray();
          int k=vars->a.size();
          for (int i=vars->a.size(); i--;)
            if (vars->a[i]->isInt())
              k--;
          IntVarArgs va(k);
          k=0;
          for (unsigned int i=0; i<vars->a.size(); i++) {
            if (vars->a[i]->isInt())
              continue;
            va[k++] = iv[vars->a[i]->getIntVar()];
            iv_searched[vars->a[i]->getIntVar()] = true;
          }
          assign(*this, va, ann2asnivalsel(args->a[1],rnd), nullptr,
                &varValPrint<IntVar>);
        } else if (flatAnn[i]->isCall("bool_search")) {
          AST::Call *call = flatAnn[i]->getCall("bool_search");
          AST::Array *args = call->getArgs(4);
          AST::Array *vars = args->a[0]->getArray();
          int k=vars->a.size();
          for (int i=vars->a.size(); i--;)
            if (vars->a[i]->isBool())
              k--;
          BoolVarArgs va(k);
          k=0;
          std::vector<std::string> names;
          for (unsigned int i=0; i<vars->a.size(); i++) {
            if (vars->a[i]->isBool())
              continue;
            va[k++] = bv[vars->a[i]->getBoolVar()];
            bv_searched[vars->a[i]->getBoolVar()] = true;
            names.push_back(vars->a[i]->getVarName());
          }
          std::string r0, r1;
          {
            BrancherGroup bg;
            branch(bg(*this), va,
                   ann2bvarsel(args->a[1],rnd,decay, bm),
                   ann2bvalsel(args->a[2],r0,r1,rnd, bm),
                   nullptr,
                   &varValPrint<BoolVar>);
            branchInfo.add(bg,r0,r1,names);
          }
        } else if (flatAnn[i]->isCall("int_default_search")) {
          AST::Call *call = flatAnn[i]->getCall("int_default_search");
          AST::Array *args = call->getArgs(2);
          def_int_varsel = ann2ivarsel(args->a[0],rnd,decay, bm);
          def_int_valsel = ann2ivalsel(args->a[1],
                                       def_int_rel_left,def_int_rel_right,rnd, bm);
        } else if (flatAnn[i]->isCall("bool_default_search")) {
          AST::Call *call = flatAnn[i]->getCall("bool_default_search");
          AST::Array *args = call->getArgs(2);
          def_bool_varsel = ann2bvarsel(args->a[0],rnd,decay, bm);
          def_bool_valsel = ann2bvalsel(args->a[1],
                                        def_bool_rel_left,def_bool_rel_right,
                                        rnd, bm);
        } else if (flatAnn[i]->isCall("set_search")) {
#ifdef GECODE_HAS_SET_VARS
          AST::Call *call = flatAnn[i]->getCall("set_search");
          AST::Array *args = call->getArgs(4);
          AST::Array *vars = args->a[0]->getArray();
          int k=vars->a.size();
          for (int i=vars->a.size(); i--;)
            if (vars->a[i]->isSet())
              k--;
          SetVarArgs va(k);
          k=0;
          std::vector<std::string> names;
          for (unsigned int i=0; i<vars->a.size(); i++) {
            if (vars->a[i]->isSet())
              continue;
            va[k++] = sv[vars->a[i]->getSetVar()];
            sv_searched[vars->a[i]->getSetVar()] = true;
            names.push_back(vars->a[i]->getVarName());
          }
          std::string r0, r1;
          {
            BrancherGroup bg;
            branch(bg(*this), va,
                   ann2svarsel(args->a[1],rnd,decay, bm),
                   ann2svalsel(args->a[2],r0,r1,rnd, bm),
                   nullptr,
                   &varValPrint<SetVar>);
            branchInfo.add(bg,r0,r1,names);
          }
#else
          if (!ignoreUnknown) {
            err << "Warning, ignored search annotation: ";
            flatAnn[i]->print(err);
            err << std::endl;
          }
#endif
        } else if (flatAnn[i]->isCall("set_default_search")) {
#ifdef GECODE_HAS_SET_VARS
          AST::Call *call = flatAnn[i]->getCall("set_default_search");
          AST::Array *args = call->getArgs(2);
          def_set_varsel = ann2svarsel(args->a[0],rnd,decay, bm);
          def_set_valsel = ann2svalsel(args->a[1],
                                       def_set_rel_left,def_set_rel_right,rnd, bm);
#else
          if (!ignoreUnknown) {
            err << "Warning, ignored search annotation: ";
            flatAnn[i]->print(err);
            err << std::endl;
          }
#endif
        } else if (flatAnn[i]->isCall("float_default_search")) {
#ifdef GECODE_HAS_FLOAT_VARS
          AST::Call *call = flatAnn[i]->getCall("float_default_search");
          AST::Array *args = call->getArgs(2);
          def_float_varsel = ann2fvarsel(args->a[0],rnd,decay, bm);
          def_float_valsel = ann2fvalsel(args->a[1],
                                         def_float_rel_left,def_float_rel_right, bm);
#else
          if (!ignoreUnknown) {
            err << "Warning, ignored search annotation: ";
            flatAnn[i]->print(err);
            err << std::endl;
          }
#endif
        } else if (flatAnn[i]->isCall("float_search")) {
#ifdef GECODE_HAS_FLOAT_VARS
          AST::Call *call = flatAnn[i]->getCall("float_search");
          AST::Array *args = call->getArgs(5);
          AST::Array *vars = args->a[0]->getArray();
          int k=vars->a.size();
          for (int i=vars->a.size(); i--;)
            if (vars->a[i]->isFloat())
              k--;
          FloatVarArgs va(k);
          k=0;
          std::vector<std::string> names;
          for (unsigned int i=0; i<vars->a.size(); i++) {
            if (vars->a[i]->isFloat())
              continue;
            va[k++] = fv[vars->a[i]->getFloatVar()];
            fv_searched[vars->a[i]->getFloatVar()] = true;
            names.push_back(vars->a[i]->getVarName());
          }
          std::string r0, r1;
          {
            BrancherGroup bg;
            branch(bg(*this), va,
                   ann2fvarsel(args->a[2],rnd,decay, bm),
                   ann2fvalsel(args->a[3],r0,r1, bm),
                   nullptr,
                   &varValPrintF);
            branchInfo.add(bg,r0,r1,names);
          }
#else
          if (!ignoreUnknown) {
            err << "Warning, ignored search annotation: ";
            flatAnn[i]->print(err);
            err << std::endl;
          }
#endif
        } else {
          if (!ignoreUnknown) {
            err << "Warning, ignored search annotation: ";
            flatAnn[i]->print(err);
            err << std::endl;
          }
        }
      }
    }

    // If relax and reconstruct is not set: Use default values obtained in storeConstraintInformation:
    if (_lnsAnnType != LNSAnnType::FULL_LNS_ANN){
      // iv_lns = iv_lns_default;
      (*_lns) = default_lns;
    }

    int introduced = 0;
    int funcdep = 0;
    int searched = 0;
    for (int i=iv.size(); i--;) {
      if (iv_searched[i] || (_method != SAT && _optVarIsInt && _optVar==i)) {
        searched++;
      } else if (iv_introduced[2*i]) {
        if (iv_introduced[2*i+1]) {
          funcdep++;
        } else {
          introduced++;
        }
      }
    }
    std::vector<std::string> iv_sol_names(iv.size()-(introduced+funcdep+searched));
    IntVarArgs iv_sol(iv.size()-(introduced+funcdep+searched));
    std::vector<std::string> iv_tmp_names(introduced);
    IntVarArgs iv_tmp(introduced);
    for (int i=iv.size(), j=0, k=0; i--;) {
      if (iv_searched[i] || (_method != SAT && _optVarIsInt && _optVar==i))
        continue;
      if (iv_introduced[2*i]) {
        if (!iv_introduced[2*i+1]) {
          iv_tmp_names[j] = p.intVarName(i);
          iv_tmp[j++] = iv[i];
        }
      } else {
        iv_sol_names[k] = p.intVarName(i);
        iv_sol[k++] = iv[i];
      }
    }

    introduced = 0;
    funcdep = 0;
    searched = 0;
    for (int i=bv.size(); i--;) {
      if (bv_searched[i]) {
        searched++;
      } else if (bv_introduced[2*i]) {
        if (bv_introduced[2*i+1]) {
          funcdep++;
        } else {
          introduced++;
        }
      }
    }
    std::vector<std::string> bv_sol_names(bv.size()-(introduced+funcdep+searched));
    BoolVarArgs bv_sol(bv.size()-(introduced+funcdep+searched));
    BoolVarArgs bv_tmp(introduced);
    std::vector<std::string> bv_tmp_names(introduced);
    for (int i=bv.size(), j=0, k=0; i--;) {
      if (bv_searched[i])
        continue;
      if (bv_introduced[2*i]) {
        if (!bv_introduced[2*i+1]) {
          bv_tmp_names[j] = p.boolVarName(i);
          bv_tmp[j++] = bv[i];
        }
      } else {
        bv_sol_names[k] = p.boolVarName(i);
        bv_sol[k++] = bv[i];
      }
    }

    if (iv_sol.size() > 0 && bv_sol.size() > 0) {
      branch(*this, iv_sol, bv_sol, def_intbool_varsel, def_int_valsel);
    } else if (iv_sol.size() > 0) {
      BrancherGroup bg;
      branch(bg(*this), iv_sol, def_int_varsel, def_int_valsel, nullptr,
             &varValPrint<IntVar>);
      branchInfo.add(bg,def_int_rel_left,def_int_rel_right,iv_sol_names);
    } else if (bv_sol.size() > 0) {
      BrancherGroup bg;
      branch(bg(*this), bv_sol, def_bool_varsel, def_bool_valsel, nullptr,
             &varValPrint<BoolVar>);
      branchInfo.add(bg,def_bool_rel_left,def_bool_rel_right,bv_sol_names);
    }
#ifdef GECODE_HAS_FLOAT_VARS
    introduced = 0;
    funcdep = 0;
    searched = 0;
    for (int i=fv.size(); i--;) {
      if (fv_searched[i] || (_method != SAT && !_optVarIsInt && _optVar==i)) {
        searched++;
      } else if (fv_introduced[2*i]) {
        if (fv_introduced[2*i+1]) {
          funcdep++;
        } else {
          introduced++;
        }
      }
    }
    std::vector<std::string> fv_sol_names(fv.size()-(introduced+funcdep+searched));
    FloatVarArgs fv_sol(fv.size()-(introduced+funcdep+searched));
    FloatVarArgs fv_tmp(introduced);
    std::vector<std::string> fv_tmp_names(introduced);
    for (int i=fv.size(), j=0, k=0; i--;) {
      if (fv_searched[i] || (_method != SAT && !_optVarIsInt && _optVar==i))
        continue;
      if (fv_introduced[2*i]) {
        if (!fv_introduced[2*i+1]) {
          fv_tmp_names[j] = p.floatVarName(i);
          fv_tmp[j++] = fv[i];
        }
      } else {
        fv_sol_names[k] = p.floatVarName(i);
        fv_sol[k++] = fv[i];
      }
    }

    if (fv_sol.size() > 0) {
      BrancherGroup bg;
      branch(bg(*this), fv_sol, def_float_varsel, def_float_valsel, nullptr,
             &varValPrintF);
      branchInfo.add(bg,def_float_rel_left,def_float_rel_right,fv_sol_names);
    }
#endif
#ifdef GECODE_HAS_SET_VARS
    introduced = 0;
    funcdep = 0;
    searched = 0;
    for (int i=sv.size(); i--;) {
      if (sv_searched[i]) {
        searched++;
      } else if (sv_introduced[2*i]) {
        if (sv_introduced[2*i+1]) {
          funcdep++;
        } else {
          introduced++;
        }
      }
    }
    std::vector<std::string> sv_sol_names(sv.size()-(introduced+funcdep+searched));
    SetVarArgs sv_sol(sv.size()-(introduced+funcdep+searched));
    SetVarArgs sv_tmp(introduced);
    std::vector<std::string> sv_tmp_names(introduced);
    for (int i=sv.size(), j=0, k=0; i--;) {
      if (sv_searched[i])
        continue;
      if (sv_introduced[2*i]) {
        if (!sv_introduced[2*i+1]) {
          sv_tmp_names[j] = p.setVarName(i);
          sv_tmp[j++] = sv[i];
        }
      } else {
        sv_sol_names[k] = p.setVarName(i);
        sv_sol[k++] = sv[i];
      }
    }

    if (sv_sol.size() > 0) {
      BrancherGroup bg;
      branch(bg(*this), sv_sol, def_set_varsel, def_set_valsel, nullptr,
             &varValPrint<SetVar>);
      branchInfo.add(bg,def_set_rel_left,def_set_rel_right,sv_sol_names);

    }
#endif
    iv_aux = IntVarArray(*this, iv_tmp);
    bv_aux = BoolVarArray(*this, bv_tmp);
    int n_aux = iv_aux.size() + bv_aux.size();
#ifdef GECODE_HAS_SET_VARS
    sv_aux = SetVarArray(*this, sv_tmp);
    n_aux += sv_aux.size();
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    fv_aux = FloatVarArray(*this, fv_tmp);
    n_aux += fv_aux.size();
#endif

    if (n_aux > 0) {
      if (_method == SAT) {
        AuxVarBrancher::post(*this, def_int_varsel, def_int_valsel,
                             def_bool_varsel, def_bool_valsel
#ifdef GECODE_HAS_SET_VARS
                             , def_set_varsel, def_set_valsel
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                             , def_float_varsel, def_float_valsel
#endif
                             );
      } else {
        {
          BrancherGroup bg;
          branch(bg(*this),iv_aux,def_int_varsel,def_int_valsel, nullptr,
                 &varValPrint<IntVar>);
          branchInfo.add(bg,def_int_rel_left,def_int_rel_right,iv_tmp_names);
        }
        {
          BrancherGroup bg;
          branch(bg(*this),bv_aux,def_bool_varsel,def_bool_valsel, nullptr,
                 &varValPrint<BoolVar>);
          branchInfo.add(bg,def_bool_rel_left,def_bool_rel_right,bv_tmp_names);
        }
  #ifdef GECODE_HAS_SET_VARS
        {
          BrancherGroup bg;
          branch(bg(*this),sv_aux,def_set_varsel,def_set_valsel, nullptr,
                 &varValPrint<SetVar>);
          branchInfo.add(bg,def_set_rel_left,def_set_rel_right,sv_tmp_names);
        }
  #endif
  #ifdef GECODE_HAS_FLOAT_VARS
        {
          BrancherGroup bg;
          branch(bg(*this),fv_aux,def_float_varsel,def_float_valsel, nullptr,
                 &varValPrintF);
          branchInfo.add(bg,def_float_rel_left,def_float_rel_right,fv_tmp_names);
        }
  #endif

      }
    }

    if (_method == MIN) {
      if (_optVarIsInt) {
        std::vector<std::string> names(2);
        names[0] = "total_viol";
        names[1] = p.intVarName(_optVar);
        BrancherGroup bg;
        branch(bg(*this), total_viol, INT_VAL_MIN(),
               &varValPrint<IntVar>);
        branch(bg(*this), iv[_optVar],  INT_VAL_MIN(),
               &varValPrint<IntVar>);
        branchInfo.add(bg,"=","!=", names);
      } else {
#ifdef GECODE_HAS_FLOAT_VARS
        std::vector<std::string> names(1);
        names[0] = p.floatVarName(_optVar);
        BrancherGroup bg;
        branch(bg(*this), fv[_optVar], FLOAT_VAL_SPLIT_MIN(),
               &varValPrintF);
        branchInfo.add(bg,"<=",">",names);
#endif
      }
    } else if (_method == MAX) {
      if (_optVarIsInt) {
        std::vector<std::string> names(2);
        names[0] = "total_viol";
        names[1] = p.intVarName(_optVar);
        BrancherGroup bg;
        branch(bg(*this), total_viol, INT_VAL_MIN(),
               &varValPrint<IntVar>);
        branch(bg(*this), iv[_optVar], INT_VAL_MAX(),
               &varValPrint<IntVar>);
        branchInfo.add(bg,"=","!=",names);
      } else {
#ifdef GECODE_HAS_FLOAT_VARS
        std::vector<std::string> names(1);
        names[0] = p.floatVarName(_optVar);
        BrancherGroup bg;
        branch(bg(*this), fv[_optVar], FLOAT_VAL_SPLIT_MAX(),
               &varValPrintF);
        branchInfo.add(bg,"<=",">",names);
#endif
      }
    } else {
      assert(_method == SAT);
      std::vector<std::string> names(1);
      names[0] = "total_viol";
      BrancherGroup bg;
      branch(bg(*this), total_viol, INT_VAL_MIN(),
             &varValPrint<IntVar>);
      branchInfo.add(bg,"=","!=",names);
    }
  }

  int FlatZincSpace::compareObjectiveValue(const FlatZincSpace& other) const {
    if (method() != other.method()) {
      throw std::runtime_error("compareObjectiveValue: cannot compare spaces with different methods.");
    }
    const int thisViol = viol_vars.empty() ? 0 : total_viol.val();
    const int otherViol = other.viol_vars.empty() ? 0 : other.total_viol.val();
    if (thisViol < otherViol) {
      return -1;
    }
    if (thisViol > otherViol) {
      return 1;
    }
    if (method() == SAT) {
      return 0;
    }
    if (_optVarIsInt != other._optVarIsInt) {
      throw std::runtime_error("compareObjectiveValue: cannot compare spaces with different objective variable types.");
    }
#ifdef GECODE_HAS_FLOAT_VARS
    if (!_optVarIsInt) {
      const FloatVal thisVal = fv[_optVar].min();
      const FloatVal otherVal = other.fv[other._optVar].min();
      const bool inStep = abs(thisVal - otherVal) <= step;
      if (inStep) {
        return 0;
      }
      return _method == MIN ? (thisVal < otherVal ? -1 : 1) : (thisVal > otherVal ? -1 : 1);
    }
#endif
    const int thisVal = _optVar < 0 ? 0 : iv[_optVar].val();
    const int otherVal = other._optVar < 0 ? 0 : other.iv[other._optVar].val();
    if (thisVal == otherVal) {
      return 0;
    }
    return _method == MIN ? (thisVal < otherVal ? -1 : 1) : (thisVal > otherVal ? -1 : 1);
  }

  void FlatZincSpace::populateLnsVars(const std::vector<ConExpr*>& conExpressions) {
    if (iv_lns.size() > 0 || bv_lns.size() > 0 || fv_lns.size() > 0 || sv_lns.size() > 0) {
      return;
    }
    std::vector<bool> int_vars(iv.size(), true);
    std::vector<bool> bool_vars(bv.size(), true);
    std::vector<bool> float_vars(fv.size(), true);
    std::vector<bool> set_vars(sv.size(), true);
    unsigned int iv_lns_size = iv.size();
    unsigned int bv_lns_size = bv.size();
    unsigned int fv_lns_size = fv.size();
    unsigned int sv_lns_size = sv.size();

    auto markDefinedVar = [&](AST::Node* var) -> void {
      if (var->isInt() || var->isBool() || var->isFloat() || var->isSet()) {
      } else if (var->isIntVar()) {
        iv_lns_size -= int_vars[var->getIntVar()] ? 1 : 0;
        int_vars[var->getIntVar()] = false;
      } else if (var->isBoolVar()) {
        bv_lns_size -= bool_vars[var->getBoolVar()] ? 1 : 0;
        bool_vars[var->getBoolVar()] = false;
      } else if (var->isFloatVar()) {
        fv_lns_size -= float_vars[var->getFloatVar()] ? 1 : 0;
        float_vars[var->getFloatVar()] = false;
      } else if (var->isSetVar()) {
        sv_lns_size -= set_vars[var->getSetVar()] ? 1 : 0;
        set_vars[var->getSetVar()] = false;
      }
    };

    for (const auto* ce : conExpressions) {
      if (ce->ann == nullptr || ce->ann->a.empty()) {
        continue;
      }
      for (size_t i = 0; i < ce->ann->a.size(); ++i) {
        if (!ce->ann->a[i]->isCall("defines_var") && !ce->ann->a[i]->isCall("gecode_defines_vars")) {
          continue;
        }

        const auto* call = ce->ann->a[i]->getCall(
          ce->ann->a[i]->isCall("defines_var")
          ? "defines_var"
          : "gecode_defines_vars");

        auto* var = call->args;
        if (var->isArray()) {
          const auto* varArr = var->getArray();
          for (size_t j = 0; j < varArr->a.size(); ++j) {
            markDefinedVar(varArr->a[j]);
          }
        } else {
          markDefinedVar(var);
        }
      }
    }
    iv_lns = IntVarArray(*this, iv_lns_size);
    unsigned int j = 0;
    for (unsigned int i = 0; i < int_vars.size(); ++i) {
      if (int_vars[i]) {
        iv_lns[j++] = iv[i];
      }
    }
    bv_lns = BoolVarArray(*this, bv_lns_size);
    j = 0;
    for (unsigned int i = 0; i < bv_lns.size(); ++i) {
      if (bool_vars[i]) {
        bv_lns[j++] = bv[i];
      }
    }
    fv_lns = FloatVarArray(*this, fv_lns_size);
    j = 0;
    for (unsigned int i = 0; i < fv_lns.size(); ++i) {
      if (float_vars[i]) {
        fv_lns[j++] = fv[i];
      }
    }
    sv_lns = SetVarArray(*this, sv_lns_size);
    j = 0;
    for (unsigned int i = 0; i < sv_lns.size(); ++i) {
      if (set_vars[i]) {
        sv_lns[j++] = sv[i];
      }
    }
  }

  bool FlatZincSpace::hasInitialIncumbentSolution(AST::Array* _solveAnnotations) {
    std::vector<AST::Node*> flatAnn;
    if (_solveAnnotations->isArray()) {
      flattenAnnotations(_solveAnnotations->getArray(), flatAnn);
    } else {
      flatAnn.emplace_back(_solveAnnotations);
    }

    for (unsigned int i = 0; i < flatAnn.size(); ++i) {
      if (flatAnn[i]->isCall("relax_and_reconstruct")) {
        const AST::Call *call = flatAnn[i]->getCall("relax_and_reconstruct");
        return call->args->getArray()->a.size() == 3;
      }
      if (flatAnn[i]->isCall("warm_start") || flatAnn[i]->isCall("warm_start_array")) {
        return true;
      }
    }
    return false;
  }

  void FlatZincSpace::applyInitialIncumbentSolution(AST::Array* solveAnnotations) {
    if (_incumbentSolution == nullptr) {
      throw std::runtime_error("FlatZincSpace::populateInitialIncumbentSolution: _incumbentSolution == nullptr");
    }
    if (_incumbentSolution->hasValue()) {
      throw std::runtime_error("FlatZincSpace::populateInitialIncumbentSolution: _incumbentSolution already a solution");
    }
    if (solveAnnotations == nullptr) {
      throw std::runtime_error("FlatZincSpace::populateInitialIncumbentSolution: solveAnnotations is nullptr");
    }


    std::vector<AST::Node*> flatAnn;
    if (solveAnnotations->isArray()) {
      flattenAnnotations(solveAnnotations->getArray(), flatAnn);
    } else {
      flatAnn.emplace_back(solveAnnotations);
    }

    std::vector<std::optional<int>> iv_init(iv.size(), std::optional<int>{});
    std::vector<std::optional<bool>> bv_init(bv.size(), std::optional<bool>{});
#ifdef GECODE_HAS_FLOAT_VARS
    std::vector<std::optional<FloatVal>> fv_init(fv.size(), std::optional<FloatVal>{});
#endif

    auto addWarmStart = [&](const AST::Array* varArr, const AST::Array* valArr) -> void {
      for (unsigned int i = 0; i < varArr->a.size(); ++i) {
        auto* varNode = varArr->a[i];
        auto* valNode = valArr->a[i];
        if (varNode->isIntVar()) {
          const int index = varNode->getIntVar();
          if (valNode->isInt() || valNode->isBool()) {
            const int v = valNode->isInt() ? valNode->getInt() : (valNode->isBool() ? 1 : 0);
            if (iv_init[index].has_value()) {
              if (v == iv_init[index].value()) {
                continue;
              }
              throw FlatZinc::Error("FlatZinc", "The same variable is initialized multiple times");
            }
            iv_init[index] = v;
          }
        } else if (varNode->isBoolVar()) {
          const int index = varNode->getBoolVar();
          if (valNode->isBool() || (valNode->isInt() && 0 <= valNode->getInt() && valNode->getInt() <= 1)) {
            const bool v = valNode->isBool() ? valNode->getBool() : valNode->getInt() == 1;
            if (bv_init[index].has_value()) {
              if (v == bv_init[index].value()) {
                continue;
              }
              throw FlatZinc::Error("FlatZinc", "The same variable is initialized multiple times");
            }
            bv_init[index] = v;
          }
        }
#ifdef GECODE_HAS_FLOAT_VARS
        else if (varNode->isFloatVar() && valNode->isFloat()) {
            const int index = varNode->getBoolVar();
            const FloatVal v = valNode->getFloat();
            if (fv_init[index].has_value()) {
              if (v == fv_init[index].value()) {
                continue;
              }
              throw FlatZinc::Error("FlatZinc", "The same variable is initialized multiple times");
            }
            fv_init[index] = v;
          }
#endif
        }
    };

    auto addAnnotation = [&](AST::Call* call) -> void {
      const auto* args = call->getArgs(2);
      const AST::Array *vars = args->a[0]->getArray();
      const AST::Array* vals = args->a[1]->getArray();
      if (vars->a.size() != vals->a.size()) {
        throw std::runtime_error("warm_start: initial solution size mismatch");
      }
      addWarmStart(vars, vals);
    };

    for (unsigned int i = 0; i < flatAnn.size(); ++i) {
      if (flatAnn[i]->isCall("relax_and_reconstruct")) {
        AST::Call *call = flatAnn[i]->getCall("relax_and_reconstruct");
        if (call->args->getArray()->a.size() != 3) {
          continue;
        }
        const auto* args = call->getArgs(3);
        const AST::Array *vars = args->a[0]->getArray();
        const AST::Array* vals = args->a[2]->getArray();
        if (vars->a.size() != vals->a.size()) {
          throw FlatZinc::Error("FlatZinc", "relax_and_reconstruct arguments 1 and 3 should have same size");
        }
        addWarmStart(vars, vals);
      }
      if (flatAnn[i]->isCall("warm_start")) {
        addAnnotation(flatAnn[i]->getCall("warm_start"));
      }
      if (flatAnn[i]->isCall("warm_start_array")) {
        AST::Call *call = flatAnn[i]->getCall("warm_start_array");
        const auto* args = call->getArgs(1);
        const AST::Array *wsAnnotations = args->a[0]->getArray();
        for (unsigned int j = 0; j < wsAnnotations->a.size(); ++j) {
          if (!wsAnnotations->a[j]->isCall("warm_start")) {
            throw FlatZinc::Error("FlatZinc", "warm_start_array should only contain warm_start annotations");
          }
          addAnnotation(wsAnnotations->a[i]->getCall("warm_start"));
        }
      }
    }
    for (unsigned int i = 0; i < iv_init.size(); ++i) {
      if (iv_init[i].has_value()) {
        rel(*this, iv[i], IRT_EQ, iv_init[i].value());
      }
    }
    for (unsigned int i = 0; i < bv_init.size(); ++i) {
      if (bv_init[i].has_value()) {
        rel(*this, bv[i], IRT_EQ, bv_init[i].value() == true ? 1 : 0);
      }
    }
#ifdef GECODE_HAS_FLOAT_VARS
    for (unsigned int i = 0; i < fv_init.size(); ++i) {
      if (fv_init[i].has_value()) {
        rel(*this, fv[i], FRT_EQ, fv_init[i].value());
      }
    }
#endif
    const auto stat = status();
    if (stat != SS_SOLVED) {
      throw std::runtime_error("supplied initial solution is a non-solution");
    }
  }

  AST::Array* FlatZincSpace::solveAnnotations(void) const {
    return _solveAnnotations;
  }

  void FlatZincSpace::setSolveAnnotations(AST::Array* solveAnnotations){
    _solveAnnotations = solveAnnotations;
  }

  void
  FlatZincSpace::solve(AST::Array* ann) {
    _method = SAT;
    _solveAnnotations = ann;
    last_best_objective = std::make_shared<std::pair<int, int>>(std::numeric_limits<int>::max(), 0);
  }

  void
  FlatZincSpace::minimize(int var, bool isInt, AST::Array* ann) {
    _method = MIN;
    _optVar = var;
    _optVarIsInt = isInt;
    _solveAnnotations = ann;
    last_best_objective = std::make_shared<std::pair<int, int>>(std::numeric_limits<int>::max(), std::numeric_limits<int>::max());
  }

  void
  FlatZincSpace::maximize(int var, bool isInt, AST::Array* ann) {
    _method = MAX;
    _optVar = var;
    _optVarIsInt = isInt;
    _solveAnnotations = ann;
    last_best_objective = std::make_shared<std::pair<int, int>>(std::numeric_limits<int>::max(), std::numeric_limits<int>::min());
  }

  FlatZincSpace::~FlatZincSpace(void) {
    delete _initData;
    if (constraints.size() > 0) {
      for (ConExpr* ce : constraints){
        delete ce;
        ce = nullptr;
      }
    }
    
  }

#ifdef GECODE_HAS_GIST

  /**
   * \brief Traits class for search engines
   */
  template<class Engine>
  class GistEngine {
  };

  /// Specialization for DFS
  template<typename S>
  class GistEngine<DFS<S> > {
  public:
    static void explore(S* root, const FlatZincOptions& opt,
                        Gist::Inspector* i, Gist::Comparator* c) {
      Gecode::Gist::Options o;
      o.c_d = opt.c_d(); o.a_d = opt.a_d();
      o.inspect.click(i);
      o.inspect.compare(c);
      (void) Gecode::Gist::dfs(root, o);
    }
  };

  /// Specialization for BAB
  template<typename S>
  class GistEngine<BAB<S> > {
  public:
    static void explore(S* root, const FlatZincOptions& opt,
                        Gist::Inspector* i, Gist::Comparator* c) {
      Gecode::Gist::Options o;
      o.c_d = opt.c_d(); o.a_d = opt.a_d();
      o.inspect.click(i);
      o.inspect.compare(c);
      (void) Gecode::Gist::bab(root, o);
    }
  };

  /// \brief An inspector for printing simple text output
  template<class S>
  class FZPrintingInspector
   : public Gecode::Gist::TextOutput, public Gecode::Gist::Inspector {
  private:
    const Printer& p;
  public:
    /// Constructor
    FZPrintingInspector(const Printer& p0);
    /// Use the print method of the template class S to print a space
    virtual void inspect(const Space& node);
    /// Finalize when Gist exits
    virtual void finalize(void);
  };

  template<class S>
  FZPrintingInspector<S>::FZPrintingInspector(const Printer& p0)
  : TextOutput("Gecode/FlatZinc"), p(p0) {}

  template<class S>
  void
  FZPrintingInspector<S>::inspect(const Space& node) {
    init();
    dynamic_cast<const S&>(node).print(getStream(), p);
    getStream() << std::endl;
  }

  template<class S>
  void
  FZPrintingInspector<S>::finalize(void) {
    Gecode::Gist::TextOutput::finalize();
  }

  template<class S>
  class FZPrintingComparator
  : public Gecode::Gist::VarComparator<S> {
  private:
    const Printer& p;
  public:
    /// Constructor
    FZPrintingComparator(const Printer& p0);

    /// Use the compare method of the template class S to compare two spaces
    virtual void compare(const Space& s0, const Space& s1);
  };

  template<class S>
  FZPrintingComparator<S>::FZPrintingComparator(const Printer& p0)
  : Gecode::Gist::VarComparator<S>("Gecode/FlatZinc"), p(p0) {}

  template<class S>
  void
  FZPrintingComparator<S>::compare(const Space& s0, const Space& s1) {
    this->init();
    try {
      dynamic_cast<const S&>(s0).compare(dynamic_cast<const S&>(s1),
                                         this->getStream(), p);
    } catch (Exception& e) {
      this->getStream() << "Exception: " << e.what();
    }
    this->getStream() << std::endl;
  }

#endif

  template<template<class> class Engine>
  void
  FlatZincSpace::runEngine(std::ostream& out, const Printer& p,
                           const FlatZincOptions& opt, Support::Timer& t_total) {
    
    if (opt.restart()==RM_NONE) {
      runMeta<Engine,Driver::EngineToMeta>(out,p,opt,t_total);
    } 
    else {
      runMeta<Engine,RBS>(out,p,opt,t_total);
    }
  }

#ifdef GECODE_HAS_CPPROFILER

  class FlatZincGetInfo : public CPProfilerSearchTracer::GetInfo {
  public:
    const Printer& p;
    FlatZincGetInfo(const Printer& printer) : p(printer) {}
    virtual std::string
    getInfo(const Space& space) const {
      std::stringstream ss;
      if (const FlatZincSpace* fz_space = dynamic_cast<const FlatZincSpace*>(&space)) {
        ss << "{\n\t\"domains\": \"";
        ss << fz_space->getDomains(p);
        ss << "\"\n}";
      }
      return ss.str();
    }
    ~FlatZincGetInfo(void) {};
  };

  void printIntVar(std::ostream& os, const std::string name, const Int::IntView& x) {
    os << "var ";
    if (x.assigned()) {
      os << "int: " << name << " = " << x.val() << ";";
    } else if (x.range()) {
      os << x.min() << ".." << x.max() << ": " << name << ";";
    } else {
      os << "array_union([";
      Gecode::Int::ViewRanges<Int::IntView> r(x);
      while (true) {
        os << r.min() << ".." << r.max();
        ++r;
        if (!r()) break;
        os << ',';
      }
      os << "]): " << name << ";";
    }
    os << "\n";
  }
  void printBoolVar(std::ostream& os, const std::string name, const BoolVar& b) {
    os << "var bool: " << name;
    if(b.assigned())
      os << " = " << (b.val() ? "true" : "false");
    os << ";\n";
  }
#ifdef GECODE_HAS_FLOAT_VARS
  void printFloatVar(std::ostream& os, const std::string name, const Float::FloatView& f) {
    os << "var ";
    if(f.assigned())
      os << "float: " << name << " = " << f.med() << ";";
    else
      os << f.min() << ".." << f.max() << ": " << name << ";";
    os << "\n";
  }
#endif
  std::string FlatZincSpace::getDomains(const Printer& p) const {
    std::ostringstream oss;

    for (int i = 0; i < iv.size(); i++)
      printIntVar(oss, p.intVarName(i), iv[i]);

    for (int i = 0; i < bv.size(); i++)
      printBoolVar(oss, p.boolVarName(i), bv[i]);

#ifdef GECODE_HAS_FLOAT_VARS
    for (int i = 0; i < fv.size(); i++)
      printFloatVar(oss, p.floatVarName(i), fv[i]);
#endif
#ifdef GECODE_HAS_SET_VARS
    for (int i = 0; i < sv.size(); i++)
      oss << "var " << sv[i] << ": " << p.setVarName(i) << ";" << std::endl;
#endif

    return oss.str();
  }

#endif


  template<template<class> class Engine,
           template<class,template<class> class> class Meta>
  void
  FlatZincSpace::runMeta(std::ostream& out, const Printer& p,
                         const FlatZincOptions& opt, Support::Timer& t_total) {
    #ifdef GECODE_HAS_GIST
        if (opt.mode() == SM_GIST) {
          FZPrintingInspector<FlatZincSpace> pi(p);
          FZPrintingComparator<FlatZincSpace> pc(p);
          (void) GistEngine<Engine<FlatZincSpace> >::explore(this,opt,&pi,&pc);
          return;
        }
    #endif
    StatusStatistics sstat;
    unsigned int n_p = 0;
    Support::Timer t_solve;
    t_solve.start();
    if (status(sstat) != SS_FAILED) {
      n_p = PropagatorGroup::all.size(*this);
    }
    Search::Options o;
    o.stop = Driver::CombinedStop::create(opt.node(), opt.fail(), opt.time(), opt.restart_limit(),
                                          true);
    o.c_d = opt.c_d();
    o.a_d = opt.a_d();

#ifdef GECODE_HAS_CPPROFILER
    if (opt.profiler_port()) {
      FlatZincGetInfo* getInfo = nullptr;
      if (opt.profiler_info())
        getInfo = new FlatZincGetInfo(p);
      o.tracer = new CPProfilerSearchTracer(opt.profiler_id(),
                                            opt.name(), opt.profiler_port(),
                                            getInfo);
    }

#endif

#ifdef GECODE_HAS_FLOAT_VARS
    step = opt.step();
#endif
    o.numThreads = opt.threads();
    o.nogoods_limit = opt.nogoods() ? opt.nogoods_limit() : 0;
    o.cutoff  = new Search::CutoffAppend(new Search::CutoffConstant(0), 1, Driver::createCutoff(opt));
    if (opt.interrupt())
      Driver::CombinedStop::installCtrlHandler(true);
    {
      Meta<FlatZincSpace,Engine> se(this,o);
      int noOfSolutions = opt.solutions();
      if (noOfSolutions == -1) {
        noOfSolutions = (_method == SAT) ? 1 : 0;
      }
      bool printAll = _method == SAT || opt.allSolutions() || noOfSolutions != 0;
      int findSol = noOfSolutions;
      std::shared_ptr<FlatZincSpace> sol = nullptr;
      bool hasSolution = noOfSolutions > 0;
      bool lastViolated = !viol_vars.empty();
      bool hasPrinted = false;
      while (auto next_sol = std::shared_ptr<FlatZincSpace>(se.next())) {
        --findSol;
        if (lastViolated) {
          out << "%% Violation: " << next_sol->total_viol << std::endl;
          lastViolated = next_sol->total_viol.val() > 0;
        }
        const bool isSatisfied = next_sol->viol_vars.empty() || next_sol->total_viol.val() == 0;
        const int sol_comp = (sol == nullptr || _method == SAT) ? -1 : next_sol->compareObjectiveValue(*sol);
        assert(sol_comp <= 0);
        hasPrinted = isSatisfied && (_method == SAT || (printAll && sol_comp < 0) || findSol == 0);
        if (hasPrinted) {
          next_sol->print(out, p);
          out << "----------" << std::endl;
        }
        hasSolution = hasSolution || isSatisfied;
        if (sol_comp < 0) {
          sol = next_sol;
        }
        if (hasSolution && _method == SAT) {
          break;
        }
      }
      if (sol != nullptr && hasSolution && !hasPrinted) {
        sol->print(out, p);
      }
      if (!se.stopped()) {
        if (noOfSolutions > 0 || hasSolution) {
          out << "==========" << std::endl;
        } else {
          out << "=====UNSATISFIABLE=====" << std::endl;
        }
      } else if (!hasSolution && noOfSolutions <= 0) {
        out << "=====UNKNOWN=====" << std::endl;
      }
      if (opt.interrupt())
        Driver::CombinedStop::installCtrlHandler(false);
      if (opt.mode() == SM_STAT) {
        Gecode::Search::Statistics stat = se.statistics();
        double totalTime = (t_total.stop() / 1000.0);
        double solveTime = (t_solve.stop() / 1000.0);
        double initTime = totalTime - solveTime;
        out << std::endl
            << "%%%mzn-stat: initTime=" << initTime
            << std::endl;
        out << "%%%mzn-stat: solveTime=" << solveTime
            << std::endl;
        out << "%%%mzn-stat: solutions="
            << std::abs(noOfSolutions - findSol) << std::endl
            << "%%%mzn-stat: variables="
            << (intVarCount + boolVarCount + setVarCount) << std::endl
            << "%%%mzn-stat: propagators=" << n_p << std::endl
            << "%%%mzn-stat: propagations=" << sstat.propagate+stat.propagate << std::endl
            << "%%%mzn-stat: nodes=" << stat.node << std::endl
            << "%%%mzn-stat: failures=" << stat.fail << std::endl
            << "%%%mzn-stat: restarts=" << stat.restart << std::endl
            << "%%%mzn-stat: peakDepth=" << stat.depth << std::endl
            << "%%%mzn-stat: LNS type=" << (_lnsAnnType == LNSAnnType::NO_LNS_ANN ? "NO_LNS_ANN" : (_lnsAnnType == LNSAnnType::ONLY_VARS_ANN ? "ONLY_VARS_ANN" : "FULL_LNS_ANN")) << std::endl
            << "%%%mzn-stat: PBS LNS type=" << opt.pbsAssetType() << std::endl
            << "%%%mzn-stat-end" << std::endl
            << std::endl;
      }
    }
    delete o.stop;
    delete o.tracer;
  }

#ifdef GECODE_HAS_QT
  void
  FlatZincSpace::branchWithPlugin(AST::Node* ann) {
    if (AST::Call* c = dynamic_cast<AST::Call*>(ann)) {
      QString pluginName(c->id.c_str());
      if (QLibrary::isLibrary(pluginName+".dll")) {
        pluginName += ".dll";
      } else if (QLibrary::isLibrary(pluginName+".dylib")) {
        pluginName = "lib" + pluginName + ".dylib";
      } else if (QLibrary::isLibrary(pluginName+".so")) {
        // Must check .so after .dylib so that Mac OS uses .dylib
        pluginName = "lib" + pluginName + ".so";
      }
      QPluginLoader pl(pluginName);
      QObject* plugin_o = pl.instance();
      if (!plugin_o) {
        throw FlatZinc::Error("FlatZinc",
          "Error loading plugin "+pluginName.toStdString()+
          ": "+pl.errorString().toStdString());
      }
      BranchPlugin* pb = qobject_cast<BranchPlugin*>(plugin_o);
      if (!pb) {
        throw FlatZinc::Error("FlatZinc",
        "Error loading plugin "+pluginName.toStdString()+
        ": does not contain valid PluginBrancher");
      }
      pb->branch(*this, c);
    }
  }
#else
  void
  FlatZincSpace::branchWithPlugin(AST::Node*) {
    throw FlatZinc::Error("FlatZinc",
      "Branching with plugins not supported (requires Qt support)");
  }
#endif

  void FlatZincSpace::populateCombinedObjective(const FlatZincOptions& opt) {
    if (viol_vars.empty()) {
      rel(*this, total_viol, IRT_EQ, 0);
      return;
    }
    IntVarArgs v;
    for (int i = 0; i < viol_vars.size();i++){
      v << viol_vars[i];
    }
    rel(*this, total_viol == sum(v));
  }

  void
  FlatZincSpace::run(std::ostream& out, Printer& p,
                      FlatZincOptions& opt, Support::Timer& t_total) {
    
    this->populateCombinedObjective(opt);
    BranchModifier bm(false, false, false);
    this->postConstraints(constraints, false);
    this->createBranchers(p, this->solveAnnotations(), opt, false, bm);
    this->populateLnsVars(constraints);
    this->shrinkArrays(p);

    if (_method != SAT || useSoftSubsume()) {
      runEngine<BAB>(out,p,opt,t_total);
    } else {
      runEngine<DFS>(out,p,opt,t_total);
    }
  }

  void FlatZincSpace::runPBS(std::ostream& out, FlatZinc::Printer& p, FlatZincOptions& opt, Support::Timer& t_total) {
    SearchController assetSearch(this, out, p, opt, t_total);
    storeConstraintInformation(constraints);
    if (!assetSearch.init()) {
      return;
    }
    assetSearch.run();
    variable_relations = nullptr;
    variable_impacts = nullptr;
  }

  void
  FlatZincSpace::constrain(const Space& s) {
    const auto& miSpace = dynamic_cast<const FlatZincSpace&>(s);
    assert(_incumbentSolution != nullptr);
    // If PBS, update global bounds.
    const auto global_solution = _incumbentSolution->load();
    const int local_viol = miSpace.total_viol.val();
    const int best_viol = (global_solution != nullptr && global_solution->total_viol.assigned())
    ? std::min(local_viol, global_solution->total_viol.val())
    : local_viol;
    if (best_viol > 0) {
      if (_method == SAT) {
        rel(*this, total_viol, IRT_LE, best_viol);
        return;
      }
      rel(*this, total_viol, IRT_LQ, best_viol);

      BoolVar betterViol(*this, 0, 1);
      rel(*this, total_viol, IRT_LE, best_viol, betterViol);

      BoolVar betterObj(*this, 0, 1);
      const int local_objective = miSpace.iv[miSpace._optVar].val();
      const int best_objective = (global_solution != nullptr && global_solution->iv[global_solution->_optVar].assigned())
          // Make sure the global solution exists and that it is assigned.
        ? (_method == MIN
          ? std::min(local_objective, global_solution->iv[global_solution->_optVar].val())
          : std::max(local_objective, global_solution->iv[global_solution->_optVar].val()))
        : local_objective;

      rel(*this, iv[_optVar], _method == MIN ? IRT_LE : IRT_GR, best_objective, betterObj);
      rel(*this, betterViol, BOT_OR, betterObj, true);
      return;
    }
    rel(*this, total_viol, IRT_EQ, 0);
    if (_method == SAT) {
      return;
    }
    if (_optVarIsInt) {
      const int local_objective = miSpace.iv[miSpace._optVar].val();
      const int best_objective = (global_solution != nullptr && global_solution->iv[global_solution->_optVar].assigned())
          // Make sure the global solution exists and that it is assigned.
        ? (_method == MIN
          ? std::min(local_objective, global_solution->iv[global_solution->_optVar].val())
          : std::max(local_objective, global_solution->iv[global_solution->_optVar].val()))
        : local_objective;
      auto& ov = iv[_optVar];
      rel(*this, ov, _method == MIN ? IRT_LE : IRT_GR, best_objective);
      ;
    }
    else {
#ifdef GECODE_HAS_FLOAT_VARS
      const Gecode::FloatVal local_objective = dynamic_cast<const FlatZincSpace&>(s).fv[_optVar].val();
      if (global_solution != nullptr) {
        const Gecode::FloatVal global_objective = global_solution->fv[global_solution->_optVar].val();
        if (_method == MIN){
           const Gecode::FloatVal best_objective = std::min(local_objective, global_objective);
          rel(*this, fv[_optVar], FRT_LE, best_objective-step);
        }
        else if (_method == MAX){
          const Gecode::FloatVal best_objective = std::max(local_objective, global_objective);
          rel(*this, fv[_optVar], FRT_GR, best_objective+step);
        } 
      }
      else{
        if (_method == MIN){
          rel(*this, fv[_optVar], FRT_LE, local_objective-step);
        }
          
        else if (_method == MAX){
          rel(*this, fv[_optVar], FRT_GR, local_objective+step);
        }
      }

#endif
    }
  }

  std::optional<bool> FlatZincSpace::updateOnRestart(const MetaInfo& mi) {
    if (mi.type() != MetaInfo::RESTART) {
      return {};
      if (restart_data.initialized() && restart_data().mark_complete) {
        // Fail the space
        this->fail();
        // Return true to signal we are in the global search space
        return {true};
      }

      bool ret = false;
      if (on_restart_iv.size() > 0) {
        unsigned int base = 0;

        // Assign the sol_int values (use lb if no solution is known)
        const auto last = std::dynamic_pointer_cast<const FlatZincSpace>(mi.last());
        assert(last == nullptr || last->on_restart_iv.size() == restart_data().on_restart_iv_sol);
        for (unsigned int i = 0; i < restart_data().on_restart_iv_sol; ++i) {
          IntVar& outVar = on_restart_iv[base + restart_data().on_restart_iv_sol + i];
          int solVal = (last != nullptr) ? last->on_restart_iv[i].val() : on_restart_iv[base + i].min();
          rel(*this, outVar, IRT_EQ, solVal);
        }
        base += restart_data().on_restart_iv_sol * 2;

        // Assign last_val_int values
        for (size_t i = 0; i < restart_data().last_val_int.size(); ++i) {
          rel(*this, on_restart_iv[base + i], IRT_EQ, restart_data().last_val_int[i]);
        }
        base += restart_data().last_val_int.size();

        // Assign uniform_int random values
        for (size_t i = 0; i < restart_data().uniform_range_int.size(); ++i) {
          const auto& range = restart_data().uniform_range_int[i];
          const int rndVal = range.first + _random(range.second - range.first);
          rel(*this, on_restart_iv[base + i], IRT_EQ, rndVal);
        }
        base += restart_data().uniform_range_int.size();

        // Set the status value
        if (restart_data().on_restart_status) {
          assert(base == on_restart_iv.size() - 1);
          IntVar& restart_status = on_restart_iv[base];
          switch(mi.reason()) {
            case MetaInfo::RR_INIT:
              assert(!mi.last());
              rel(*this, restart_status, IRT_EQ, 1); // 1: START
              break;
            case MetaInfo::RR_SOL:
              assert(mi.solution() > 0);
              rel(*this, restart_status, IRT_EQ, 4); // 4: SAT
              break;
            case MetaInfo::RR_CMPL:
              rel(*this, restart_status, IRT_EQ, 3); // 3: UNSAT
              break;
            default:
              assert(mi.reason() == MetaInfo::RR_LIM);
              rel(*this, restart_status, IRT_EQ, 2); // 2: UNKNOWN
              break;
          }
          base += 1;
        }
        assert(base == on_restart_iv.size());

        // Reduce on_restart_iv to only the variables required in a solution
        IntVarArray tmp(*this, restart_data().on_restart_iv_sol);
        for (int i = 0; i < restart_data().on_restart_iv_sol; ++i) {
          tmp[i] = on_restart_iv[i];
        }
        on_restart_iv = tmp;

        ret = true;
      }
      if (on_restart_bv.size() > 0) {
        unsigned int base = 0;

        // Assign the sol_bool values (use lb if no solution is known)
        const auto last = std::dynamic_pointer_cast<const FlatZincSpace>(mi.last());
        assert(last == nullptr || last->on_restart_bv.size() == restart_data().on_restart_bv_sol);
        for (int i = 0; i < restart_data().on_restart_bv_sol; ++i) {
          BoolVar& outVar = on_restart_bv[base + restart_data().on_restart_bv_sol + i];
          int solVal = (last != nullptr) ? last->on_restart_bv[i].val() : on_restart_bv[base + i].min();
          rel(*this, outVar, IRT_EQ, solVal);
        }
        base += restart_data().on_restart_bv_sol * 2;

        // Assign last_val_bool values
        for (size_t i = 0; i < restart_data().last_val_bool.size(); ++i) {
          rel(*this, on_restart_bv[base + i], IRT_EQ, restart_data().last_val_bool[i]);
        }
        base += restart_data().last_val_bool.size();
        assert(base == on_restart_bv.size());

        // Reduce on_restart_bv to only the variables required in a solution
        BoolVarArray tmp(*this, restart_data().on_restart_bv_sol);
        for (int i = 0; i < restart_data().on_restart_bv_sol; ++i) {
          tmp[i] = on_restart_bv[i];
        }
        on_restart_bv = tmp;

        ret = true;
      }
#ifdef GECODE_HAS_SET_VARS
      if (on_restart_sv.size() > 0) {
        unsigned int base = 0;

        // Assign the sol_set values (use lb if no solution is known)
        const auto last = std::dynamic_pointer_cast<const FlatZincSpace>(mi.last());
        assert(last == nullptr || last->on_restart_sv.size() == restart_data().on_restart_sv_sol);
        for (unsigned int i = 0; i < restart_data().on_restart_sv_sol; ++i) {
          SetVar& outVar = on_restart_sv[base + restart_data().on_restart_sv_sol + i];
          Set::GlbRanges<Set::SetView> lb(last != nullptr ? last->on_restart_sv[i] : on_restart_sv[base + i]);
          IntSet val(lb);
          dom(*this, outVar, SRT_EQ, val);
        }
        base += restart_data().on_restart_sv_sol * 2;

        // Assign last_val_set values
        for (size_t i = 0; i < restart_data().last_val_set.size(); ++i) {
          dom(*this, on_restart_sv[base + i], SRT_EQ, restart_data().last_val_set[i]);
        }
        base += restart_data().last_val_set.size();
        assert(base == on_restart_sv.size());

        // Reduce on_restart_sv to only the variables required in a solution
        SetVarArray tmp(*this, restart_data().on_restart_sv_sol);
        for (int i = 0; i < restart_data().on_restart_sv_sol; ++i) {
          tmp[i] = on_restart_sv[i];
        }
        on_restart_sv = tmp;

        ret = true;
      }
#endif
#ifdef GECODE_HAS_FLOAT_VARS
      if (on_restart_fv.size() > 0) {
        unsigned int base = 0;

        // Assign the sol_float values (use lb if no solution is known)
        const auto last = std::dynamic_pointer_cast<const FlatZincSpace>(mi.last());
        assert(last == nullptr || last->on_restart_fv.size() == restart_data().on_restart_fv_sol);
        for (int i = 0; i < restart_data().on_restart_fv_sol; ++i) {
          FloatVar& outVar = on_restart_fv[base + restart_data().on_restart_fv_sol + i];
          FloatVal solVal = (last != nullptr) ? last->on_restart_fv[i].val() : on_restart_fv[base + i].min();
          rel(*this, outVar, FRT_EQ, solVal);
        }
        base += restart_data().on_restart_fv_sol * 2;

        // Assign last_val_float values
        for (size_t i = 0; i < restart_data().last_val_float.size(); ++i) {
          rel(*this, on_restart_fv[base + i], FRT_EQ, restart_data().last_val_float[i]);
        }
        base += restart_data().last_val_float.size();

        // Assign uniform_float random values
        for (size_t i = 0; i < restart_data().uniform_range_float.size(); ++i) {
          const auto& range = restart_data().uniform_range_float[i];
          /* rndVal will be an element of [range.first, range.second] */
          const FloatVal rndVal = (static_cast<FloatVal>(_random(INT_MAX)) / INT_MAX)*(range.second - range.first) + range.first;
          rel(*this, on_restart_fv[base + i], FRT_EQ, rndVal);
        }
        base += restart_data().uniform_range_float.size();
        assert(base == on_restart_fv.size());

        // Reduce on_restart_fv to only the variables required in a solution
        FloatVarArray tmp(*this, restart_data().on_restart_fv_sol);
        for (int i = 0; i < restart_data().on_restart_fv_sol; ++i) {
          tmp[i] = on_restart_fv[i];
        }
        on_restart_fv = tmp;

        ret = true;
      }
#endif
      if (ret) {
        return {false};
      }
    }

    if (_lnsAnnType != FULL_LNS_ANN && mi.restart() != 0 && mi.restart() > *last_best_restart){
      const unsigned long diff = mi.restart() - *last_best_restart;
      if (*_lns >= 90 && diff > 150) {
        *_lns = 5;
      } else {
        const int change = diff > 50 ? 1 : -1;
        *_lns = std::max<int>(5, std::min<int>(90, static_cast<int>(*_lns) + change));
      }
    }
    return {};
  }


  bool
  FlatZincSpace::slave(const MetaInfo& mi) {
    auto ret = updateOnRestart(mi);
    if (ret.has_value()) {
      return *ret;
    }

    // Depending on the type of LNS, apply it and return false.
    switch (_assetType) {
      case AssetType::LNS_USER:
      {
        return LNSstrategies::random(*this, mi);
      }
      case AssetType::PGLNS:
      {
        return LNSstrategies::propagationGuided(*this, mi, 10);
      }
      case AssetType::REVPGLNS:
      {
        return LNSstrategies::reversedPropagationGuided(*this, mi, 10);
      }
      case AssetType::OBJRELLNS:
      {
        return LNSstrategies::objectiveRelaxation(*this, mi);
      }
      case AssetType::CIGLNS:
      {
        return LNSstrategies::costImpactGuided(*this, mi, 2, 0.5);
      }
      case AssetType::SVRLNS:
      {
        return LNSstrategies::staticVariableRelation(*this, mi);
      }
      default:
      {
        return true;
      }
    }
  }

  Space*
  FlatZincSpace::copy(void) {
    return new FlatZincSpace(*this);
  }

  FlatZincSpace::Meth
  FlatZincSpace::method(void) const {
    return _method;
  }

  int
  FlatZincSpace::optVar(void) const {
    return _optVar;
  }

  bool
  FlatZincSpace::optVarIsInt(void) const {
    return _optVarIsInt;
  }

  void
  FlatZincSpace::print(std::ostream& out, const Printer& p) const {
    p.print(out, iv, bv
#ifdef GECODE_HAS_SET_VARS
    , sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    , fv
#endif
    );
  }

  void
  FlatZincSpace::compare(const Space& s, std::ostream& out) const {
    (void) s; (void) out;
#ifdef GECODE_HAS_GIST
    const FlatZincSpace& fs = dynamic_cast<const FlatZincSpace&>(s);
    for (int i = 0; i < iv.size(); ++i) {
      std::stringstream ss;
      ss << "iv[" << i << "]";
      std::string result(Gecode::Gist::Comparator::compare(ss.str(), iv[i],
                                                           fs.iv[i]));
      if (result.length() > 0) out << result << std::endl;
    }
    for (int i = 0; i < bv.size(); ++i) {
      std::stringstream ss;
      ss << "bv[" << i << "]";
      std::string result(Gecode::Gist::Comparator::compare(ss.str(), bv[i],
                                                           fs.bv[i]));
      if (result.length() > 0) out << result << std::endl;
    }
#ifdef GECODE_HAS_SET_VARS
    for (int i = 0; i < sv.size(); ++i) {
      std::stringstream ss;
      ss << "sv[" << i << "]";
      std::string result(Gecode::Gist::Comparator::compare(ss.str(), sv[i],
                                                           fs.sv[i]));
      if (result.length() > 0) out << result << std::endl;
    }
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    for (int i = 0; i < fv.size(); ++i) {
      std::stringstream ss;
      ss << "fv[" << i << "]";
      std::string result(Gecode::Gist::Comparator::compare(ss.str(), fv[i],
                                                           fs.fv[i]));
      if (result.length() > 0) out << result << std::endl;
    }
#endif
#endif
  }

  void
  FlatZincSpace::compare(const FlatZincSpace& s, std::ostream& out,
                         const Printer& p) const {
    p.printDiff(out, iv, s.iv, bv, s.bv
#ifdef GECODE_HAS_SET_VARS
     , sv, s.sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
     , fv, s.fv
#endif
    );
  }

  void
  FlatZincSpace::shrinkArrays(Printer& p) {
    p.shrinkArrays(*this, _optVar, _optVarIsInt, iv, bv
#ifdef GECODE_HAS_SET_VARS
    , sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    , fv
#endif
    );
  }

  IntArgs
  FlatZincSpace::arg2intargs(AST::Node* arg, int offset) {
    AST::Array* a = arg->getArray();
    IntArgs ia(a->a.size()+offset);
    for (int i=offset; i--;)
      ia[i] = 0;
    for (int i=a->a.size(); i--;)
      ia[i+offset] = a->a[i]->getInt();
    return ia;
  }
  TupleSet
  FlatZincSpace::arg2tupleset(const IntArgs& a, int noOfVars) {
    int noOfTuples = a.size() == 0 ? 0 : (a.size()/noOfVars);

    // Build TupleSet
    TupleSet ts(noOfVars);
    for (int i=0; i<noOfTuples; i++) {
      IntArgs t(noOfVars);
      for (int j=0; j<noOfVars; j++) {
        t[j] = a[i*noOfVars+j];
      }
      ts.add(t);
    }
    ts.finalize();

    if (_initData) {
      FlatZincSpaceInitData::TupleSetSet::iterator it = _initData->tupleSetSet.find(ts);
      if (it != _initData->tupleSetSet.end()) {
        return *it;
      }
      _initData->tupleSetSet.insert(ts);
    }


    return ts;
  }
  IntSharedArray
  FlatZincSpace::arg2intsharedarray(AST::Node* arg, int offset) {
    IntArgs ia(arg2intargs(arg,offset));
    SharedArray<int> sia(ia);
    if (_initData) {
      FlatZincSpaceInitData::IntSharedArraySet::iterator it = _initData->intSharedArraySet.find(sia);
      if (it != _initData->intSharedArraySet.end()) {
        return *it;
      }
      _initData->intSharedArraySet.insert(sia);
    }

    return sia;
  }
  IntArgs
  FlatZincSpace::arg2boolargs(AST::Node* arg, int offset) {
    AST::Array* a = arg->getArray();
    IntArgs ia(a->a.size()+offset);
    for (int i=offset; i--;)
      ia[i] = 0;
    for (int i=a->a.size(); i--;)
      ia[i+offset] = a->a[i]->getBool();
    return ia;
  }
  IntSharedArray
  FlatZincSpace::arg2boolsharedarray(AST::Node* arg, int offset) {
    IntArgs ia(arg2boolargs(arg,offset));
    SharedArray<int> sia(ia);
    if (_initData) {
      FlatZincSpaceInitData::IntSharedArraySet::iterator it = _initData->intSharedArraySet.find(sia);
      if (it != _initData->intSharedArraySet.end()) {
        return *it;
      }
      _initData->intSharedArraySet.insert(sia);
    }

    return sia;
  }
  IntSet
  FlatZincSpace::arg2intset(AST::Node* n) {
    AST::SetLit* sl = n->getSet();
    IntSet d;
    if (sl->interval) {
      d = IntSet(sl->min, sl->max);
    } else {
      Region re;
      int* is = re.alloc<int>(static_cast<unsigned long int>(sl->s.size()));
      for (int i=sl->s.size(); i--; )
        is[i] = sl->s[i];
      d = IntSet(is, sl->s.size());
    }
    return d;
  }
  IntSetArgs
  FlatZincSpace::arg2intsetargs(AST::Node* arg, int offset) {
    AST::Array* a = arg->getArray();
    if (a->a.size() == 0) {
      IntSetArgs emptyIa(0);
      return emptyIa;
    }
    IntSetArgs ia(a->a.size()+offset);
    for (int i=offset; i--;)
      ia[i] = IntSet::empty;
    for (int i=a->a.size(); i--;) {
      ia[i+offset] = arg2intset(a->a[i]);
    }
    return ia;
  }
  IntVarArgs
  FlatZincSpace::arg2intvarargs(AST::Node* arg, int offset) {
    AST::Array* a = arg->getArray();
    if (a->a.size() == 0) {
      IntVarArgs emptyIa(0);
      return emptyIa;
    }
    IntVarArgs ia(a->a.size()+offset);
    for (int i=offset; i--;)
      ia[i] = IntVar(*this, 0, 0);
    for (int i=a->a.size(); i--;) {
      if (a->a[i]->isIntVar()) {
        ia[i+offset] = iv[a->a[i]->getIntVar()];
      } else {
        int value = a->a[i]->getInt();
        IntVar iv(*this, value, value);
        ia[i+offset] = iv;
      }
    }
    return ia;
  }
  BoolVarArgs
  FlatZincSpace::arg2boolvarargs(AST::Node* arg, int offset, int siv) {
    AST::Array* a = arg->getArray();
    if (a->a.size() == 0) {
      BoolVarArgs emptyIa(0);
      return emptyIa;
    }
    BoolVarArgs ia(a->a.size()+offset-(siv==-1?0:1));
    for (int i=offset; i--;)
      ia[i] = BoolVar(*this, 0, 0);
    for (int i=0; i<static_cast<int>(a->a.size()); i++) {
      if (i==siv)
        continue;
      if (a->a[i]->isBool()) {
        bool value = a->a[i]->getBool();
        BoolVar iv(*this, value, value);
        ia[offset++] = iv;
      } else if (a->a[i]->isIntVar() &&
                 aliasBool2Int(a->a[i]->getIntVar()) != -1) {
        ia[offset++] = bv[aliasBool2Int(a->a[i]->getIntVar())];
      } else {
        ia[offset++] = bv[a->a[i]->getBoolVar()];
      }
    }
    return ia;
  }
  BoolVar
  FlatZincSpace::arg2BoolVar(AST::Node* n) {
    BoolVar x0;
    if (n->isBool()) {
      x0 = BoolVar(*this, n->getBool(), n->getBool());
    }
    else {
      x0 = bv[n->getBoolVar()];
    }
    return x0;
  }
  IntVar
  FlatZincSpace::arg2IntVar(AST::Node* n) {
    IntVar x0;
    if (n->isIntVar()) {
      x0 = iv[n->getIntVar()];
    } else {
      x0 = IntVar(*this, n->getInt(), n->getInt());
    }
    return x0;
  }
  bool
  FlatZincSpace::isBoolArray(AST::Node* b, int& singleInt) {
    AST::Array* a = b->getArray();
    singleInt = -1;
    if (a->a.size() == 0)
      return true;
    for (int i=a->a.size(); i--;) {
      if (a->a[i]->isBoolVar() || a->a[i]->isBool()) {
      } else if (a->a[i]->isIntVar()) {
        if (aliasBool2Int(a->a[i]->getIntVar()) == -1) {
          if (singleInt != -1) {
            return false;
          }
          singleInt = i;
        }
      } else {
        return false;
      }
    }
    return singleInt==-1 || a->a.size() > 1;
  }
#ifdef GECODE_HAS_SET_VARS
  SetVar
  FlatZincSpace::arg2SetVar(AST::Node* n) {
    SetVar x0;
    if (!n->isSetVar()) {
      IntSet d = arg2intset(n);
      x0 = SetVar(*this, d, d);
    } else {
      x0 = sv[n->getSetVar()];
    }
    return x0;
  }
  SetVarArgs
  FlatZincSpace::arg2setvarargs(AST::Node* arg, int offset, int doffset,
                                const IntSet& od) {
    AST::Array* a = arg->getArray();
    SetVarArgs ia(a->a.size()+offset);
    for (int i=offset; i--;) {
      IntSet d = i<doffset ? od : IntSet::empty;
      ia[i] = SetVar(*this, d, d);
    }
    for (int i=a->a.size(); i--;) {
      ia[i+offset] = arg2SetVar(a->a[i]);
    }
    return ia;
  }
#endif
#ifdef GECODE_HAS_FLOAT_VARS
  FloatValArgs
  FlatZincSpace::arg2floatargs(AST::Node* arg, int offset) {
    AST::Array* a = arg->getArray();
    FloatValArgs fa(a->a.size()+offset);
    for (int i=offset; i--;)
      fa[i] = 0.0;
    for (int i=a->a.size(); i--;)
      fa[i+offset] = a->a[i]->getFloat();
    return fa;
  }
  FloatVarArgs
  FlatZincSpace::arg2floatvarargs(AST::Node* arg, int offset) {
    AST::Array* a = arg->getArray();
    if (a->a.size() == 0) {
      FloatVarArgs emptyFa(0);
      return emptyFa;
    }
    FloatVarArgs fa(a->a.size()+offset);
    for (int i=offset; i--;)
      fa[i] = FloatVar(*this, 0.0, 0.0);
    for (int i=a->a.size(); i--;) {
      if (a->a[i]->isFloatVar()) {
        fa[i+offset] = fv[a->a[i]->getFloatVar()];
      } else {
        double value = a->a[i]->getFloat();
        FloatVar fv(*this, value, value);
        fa[i+offset] = fv;
      }
    }
    return fa;
  }
  FloatVar
  FlatZincSpace::arg2FloatVar(AST::Node* n) {
    FloatVar x0;
    if (n->isFloatVar()) {
      x0 = fv[n->getFloatVar()];
    } else {
      x0 = FloatVar(*this, n->getFloat(), n->getFloat());
    }
    return x0;
  }
#endif
  IntPropLevel
  FlatZincSpace::ann2ipl(AST::Node* ann) {
    if (ann) {
      if (ann->hasAtom("val") || ann->hasAtom("value_propagation"))
        return IPL_VAL;
      if (ann->hasAtom("domain") || ann->hasAtom("domain_propagation"))
        return IPL_DOM;
      if (ann->hasAtom("bounds") ||
          ann->hasAtom("bounds_propagation") ||
          ann->hasAtom("boundsR") ||
          ann->hasAtom("boundsD") ||
          ann->hasAtom("boundsZ"))
        return IPL_BND;
    }
    return IPL_DEF;
  }

  DFA
  FlatZincSpace::getSharedDFA(DFA& a) {
    if (_initData) {
      FlatZincSpaceInitData::DFASet::iterator it = _initData->dfaSet.find(a);
      if (it != _initData->dfaSet.end()) {
        return *it;
      }
      _initData->dfaSet.insert(a);
    }
    return a;
  }

  void
  Printer::init(AST::Array* output) {
    _output = std::shared_ptr<AST::Array>(output);
  }

  void
  Printer::printElem(std::ostream& out,
                       AST::Node* ai,
                       const Gecode::IntVarArray& iv,
                       const Gecode::BoolVarArray& bv
#ifdef GECODE_HAS_SET_VARS
                       , const Gecode::SetVarArray& sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                       ,
                       const Gecode::FloatVarArray& fv
#endif
                       ) const {
    int k;
    if (ai->isInt(k)) {
      out << k;
    } else if (ai->isIntVar()) {
      out << iv[ai->getIntVar()];
    } else if (ai->isBoolVar()) {
      if (bv[ai->getBoolVar()].min() == 1) {
        out << "true";
      } else if (bv[ai->getBoolVar()].max() == 0) {
        out << "false";
      } else {
        out << "false..true";
      }
#ifdef GECODE_HAS_SET_VARS
    } else if (ai->isSetVar()) {
      if (!sv[ai->getSetVar()].assigned()) {
        out << sv[ai->getSetVar()];
        return;
      }
      SetVarGlbRanges svr(sv[ai->getSetVar()]);
      if (!svr()) {
        out << "{}";
        return;
      }
      int min = svr.min();
      int max = svr.max();
      ++svr;
      if (svr()) {
        SetVarGlbValues svv(sv[ai->getSetVar()]);
        int i = svv.val();
        out << "{" << i;
        ++svv;
        for (; svv(); ++svv)
          out << ", " << svv.val();
        out << "}";
      } else {
        out << min << ".." << max;
      }
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    } else if (ai->isFloatVar()) {
      if (fv[ai->getFloatVar()].assigned()) {
        FloatVal vv = fv[ai->getFloatVar()].val();
        FloatNum v;
        if (vv.singleton())
          v = vv.min();
        else if (vv < 0.0)
          v = vv.max();
        else
          v = vv.min();
        std::ostringstream oss;
        // oss << std::scientific;
        oss << std::setprecision(std::numeric_limits<double>::digits10);
        oss << v;
        if (oss.str().find(".") == std::string::npos)
          oss << ".0";
        out << oss.str();
      } else {
        out << fv[ai->getFloatVar()];
      }
#endif
    } else if (ai->isBool()) {
      out << (ai->getBool() ? "true" : "false");
    } else if (ai->isSet()) {
      AST::SetLit* s = ai->getSet();
      if (s->interval) {
        out << s->min << ".." << s->max;
      } else {
        out << "{";
        for (unsigned int i=0; i<s->s.size(); i++) {
          out << s->s[i] << (i < s->s.size()-1 ? ", " : "}");
        }
      }
    } else if (ai->isString()) {
      std::string s = ai->getString();
      for (unsigned int i=0; i<s.size(); i++) {
        if (s[i] == '\\' && i<s.size()-1) {
          switch (s[i+1]) {
          case 'n': out << "\n"; break;
          case '\\': out << "\\"; break;
          case 't': out << "\t"; break;
          default: out << "\\" << s[i+1];
          }
          i++;
        } else {
          out << s[i];
        }
      }
    }
  }

  void
  Printer::printElemDiff(std::ostream& out,
                       AST::Node* ai,
                       const Gecode::IntVarArray& iv1,
                       const Gecode::IntVarArray& iv2,
                       const Gecode::BoolVarArray& bv1,
                       const Gecode::BoolVarArray& bv2
#ifdef GECODE_HAS_SET_VARS
                       , const Gecode::SetVarArray& sv1,
                       const Gecode::SetVarArray& sv2
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                       , const Gecode::FloatVarArray& fv1,
                       const Gecode::FloatVarArray& fv2
#endif
                       ) const {
#ifdef GECODE_HAS_GIST
    using namespace Gecode::Gist;
    int k;
    if (ai->isInt(k)) {
      out << k;
    } else if (ai->isIntVar()) {
      std::string res(Comparator::compare("",iv1[ai->getIntVar()],
                                          iv2[ai->getIntVar()]));
      if (res.length() > 0) {
        res.erase(0, 1); // Remove '='
        out << res;
      } else {
        out << iv1[ai->getIntVar()];
      }
    } else if (ai->isBoolVar()) {
      std::string res(Comparator::compare("",bv1[ai->getBoolVar()],
                                          bv2[ai->getBoolVar()]));
      if (res.length() > 0) {
        res.erase(0, 1); // Remove '='
        out << res;
      } else {
        out << bv1[ai->getBoolVar()];
      }
#ifdef GECODE_HAS_SET_VARS
    } else if (ai->isSetVar()) {
      std::string res(Comparator::compare("",sv1[ai->getSetVar()],
                                          sv2[ai->getSetVar()]));
      if (res.length() > 0) {
        res.erase(0, 1); // Remove '='
        out << res;
      } else {
        out << sv1[ai->getSetVar()];
      }
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    } else if (ai->isFloatVar()) {
      std::string res(Comparator::compare("",fv1[ai->getFloatVar()],
                                          fv2[ai->getFloatVar()]));
      if (res.length() > 0) {
        res.erase(0, 1); // Remove '='
        out << res;
      } else {
        out << fv1[ai->getFloatVar()];
      }
#endif
    } else if (ai->isBool()) {
      out << (ai->getBool() ? "true" : "false");
    } else if (ai->isSet()) {
      AST::SetLit* s = ai->getSet();
      if (s->interval) {
        out << s->min << ".." << s->max;
      } else {
        out << "{";
        for (unsigned int i=0; i<s->s.size(); i++) {
          out << s->s[i] << (i < s->s.size()-1 ? ", " : "}");
        }
      }
    } else if (ai->isString()) {
      std::string s = ai->getString();
      for (unsigned int i=0; i<s.size(); i++) {
        if (s[i] == '\\' && i<s.size()-1) {
          switch (s[i+1]) {
          case 'n': out << "\n"; break;
          case '\\': out << "\\"; break;
          case 't': out << "\t"; break;
          default: out << "\\" << s[i+1];
          }
          i++;
        } else {
          out << s[i];
        }
      }
    }
#else
    (void) out;
    (void) ai;
    (void) iv1;
    (void) iv2;
    (void) bv1;
    (void) bv2;
#ifdef GECODE_HAS_SET_VARS
    (void) sv1;
    (void) sv2;
#endif
#ifdef GECODE_HAS_FLOAT_VARS
    (void) fv1;
    (void) fv2;
#endif

#endif
  }

  void
  Printer::print(std::ostream& out,
                   const Gecode::IntVarArray& iv,
                   const Gecode::BoolVarArray& bv
#ifdef GECODE_HAS_SET_VARS
                   ,
                   const Gecode::SetVarArray& sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                   ,
                   const Gecode::FloatVarArray& fv
#endif
                   ) const {
    if (_output == nullptr){
      out << "No output" << endl;
      return;
    }
      
    for (unsigned int i=0; i< _output->a.size(); i++) {
      AST::Node* ai = _output->a[i];
      if (ai->isArray()) {
        AST::Array* aia = ai->getArray();
        int size = aia->a.size();
        out << "[";
        for (int j=0; j<size; j++) {
          printElem(out,aia->a[j],iv,bv
#ifdef GECODE_HAS_SET_VARS
          ,sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
          ,fv
#endif
          );
          if (j<size-1)
            out << ", ";
        }
        out << "]";
      } else {
        printElem(out,ai,iv,bv
#ifdef GECODE_HAS_SET_VARS
        ,sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
          ,fv
#endif
        );
      }
    }
  }

  void
  Printer::printDiff(std::ostream& out,
                   const Gecode::IntVarArray& iv1,
                   const Gecode::IntVarArray& iv2,
                   const Gecode::BoolVarArray& bv1,
                   const Gecode::BoolVarArray& bv2
#ifdef GECODE_HAS_SET_VARS
                   ,
                   const Gecode::SetVarArray& sv1,
                   const Gecode::SetVarArray& sv2
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                   ,
                   const Gecode::FloatVarArray& fv1,
                   const Gecode::FloatVarArray& fv2
#endif
                   ) const {
    if (_output == nullptr)
      return;
    for (unsigned int i=0; i< _output->a.size(); i++) {
      AST::Node* ai = _output->a[i];
      if (ai->isArray()) {
        AST::Array* aia = ai->getArray();
        int size = aia->a.size();
        out << "[";
        for (int j=0; j<size; j++) {
          printElemDiff(out,aia->a[j],iv1,iv2,bv1,bv2
#ifdef GECODE_HAS_SET_VARS
            ,sv1,sv2
#endif
#ifdef GECODE_HAS_FLOAT_VARS
            ,fv1,fv2
#endif
          );
          if (j<size-1)
            out << ", ";
        }
        out << "]";
      } else {
        printElemDiff(out,ai,iv1,iv2,bv1,bv2
#ifdef GECODE_HAS_SET_VARS
          ,sv1,sv2
#endif
#ifdef GECODE_HAS_FLOAT_VARS
            ,fv1,fv2
#endif
        );
      }
    }
  }

  void
  Printer::addIntVarName(const std::string& n) {
    iv_names.push_back(n);
  }
  void
  Printer::addBoolVarName(const std::string& n) {
    bv_names.push_back(n);
  }
#ifdef GECODE_HAS_FLOAT_VARS
  void
  Printer::addFloatVarName(const std::string& n) {
    fv_names.push_back(n);
  }
#endif
#ifdef GECODE_HAS_SET_VARS
  void
  Printer::addSetVarName(const std::string& n) {
    sv_names.push_back(n);
  }
#endif

  void
  Printer::shrinkElement(AST::Node* node,
                         std::map<int,int>& iv, std::map<int,int>& bv,
                         std::map<int,int>& sv, std::map<int,int>& fv) {
    if (node->isIntVar()) {
      AST::IntVar* x = static_cast<AST::IntVar*>(node);
      if (iv.find(x->i) == iv.end()) {
        int newi = iv.size();
        iv[x->i] = newi;
      }
      x->i = iv[x->i];
    } else if (node->isBoolVar()) {
      AST::BoolVar* x = static_cast<AST::BoolVar*>(node);
      if (bv.find(x->i) == bv.end()) {
        int newi = bv.size();
        bv[x->i] = newi;
      }
      x->i = bv[x->i];
    } else if (node->isSetVar()) {
      AST::SetVar* x = static_cast<AST::SetVar*>(node);
      if (sv.find(x->i) == sv.end()) {
        int newi = sv.size();
        sv[x->i] = newi;
      }
      x->i = sv[x->i];
    } else if (node->isFloatVar()) {
      AST::FloatVar* x = static_cast<AST::FloatVar*>(node);
      if (fv.find(x->i) == fv.end()) {
        int newi = fv.size();
        fv[x->i] = newi;
      }
      x->i = fv[x->i];
    }
  }

  void
  Printer::shrinkArrays(Space& home,
                        int& optVar, bool optVarIsInt,
                        Gecode::IntVarArray& iv,
                        Gecode::BoolVarArray& bv
#ifdef GECODE_HAS_SET_VARS
                        ,
                        Gecode::SetVarArray& sv
#endif
#ifdef GECODE_HAS_FLOAT_VARS
                        ,
                        Gecode::FloatVarArray& fv
#endif
                       ) {
    if (_output == nullptr) {
      if (optVarIsInt && optVar != -1) {
        IntVar ov = iv[optVar];
        iv = IntVarArray(home, 1);
        iv[0] = ov;
        optVar = 0;
      } else {
        iv = IntVarArray(home, 0);
      }
      bv = BoolVarArray(home, 0);
#ifdef GECODE_HAS_SET_VARS
      sv = SetVarArray(home, 0);
#endif
#ifdef GECODE_HAS_FLOAT_VARS
      if (!optVarIsInt && optVar != -1) {
        FloatVar ov = fv[optVar];
        fv = FloatVarArray(home, 1);
        fv[0] = ov;
        optVar = 0;
      } else {
        fv = FloatVarArray(home,0);
      }
#endif
      return;
    }
    std::map<int,int> iv_new;
    std::map<int,int> bv_new;
    std::map<int,int> sv_new;
    std::map<int,int> fv_new;

    if (optVar != -1) {
      if (optVarIsInt)
        iv_new[optVar] = 0;
      else
        fv_new[optVar] = 0;
      optVar = 0;
    }

    for (unsigned int i=0; i< _output->a.size(); i++) {
      AST::Node* ai = _output->a[i];
      if (ai->isArray()) {
        AST::Array* aia = ai->getArray();
        for (unsigned int j=0; j<aia->a.size(); j++) {
          shrinkElement(aia->a[j],iv_new,bv_new,sv_new,fv_new);
        }
      } else {
        shrinkElement(ai,iv_new,bv_new,sv_new,fv_new);
      }
    }

    IntVarArgs iva(iv_new.size());
    std::vector<std::string> iv_names_new(iv_new.size());
    for (std::map<int,int>::iterator i=iv_new.begin(); i != iv_new.end(); ++i) {
      iva[(*i).second] = iv[(*i).first];
      iv_names_new[(*i).second] = iv_names[(*i).first];
    }
    iv = IntVarArray(home, iva);
    iv_names = iv_names_new;

    BoolVarArgs bva(bv_new.size());
    std::vector<std::string> bv_names_new(bv_new.size());
    for (std::map<int,int>::iterator i=bv_new.begin(); i != bv_new.end(); ++i) {
      bva[(*i).second] = bv[(*i).first];
      bv_names_new[(*i).second] = bv_names[(*i).first];
    }
    bv = BoolVarArray(home, bva);
    bv_names = bv_names_new;

#ifdef GECODE_HAS_SET_VARS
    SetVarArgs sva(sv_new.size());
    std::vector<std::string> sv_names_new(sv_new.size());
    for (std::map<int,int>::iterator i=sv_new.begin(); i != sv_new.end(); ++i) {
      sva[(*i).second] = sv[(*i).first];
      sv_names_new[(*i).second] = sv_names[(*i).first];
    }
    sv = SetVarArray(home, sva);
    sv_names = sv_names_new;
#endif

#ifdef GECODE_HAS_FLOAT_VARS
    FloatVarArgs fva(fv_new.size());
    std::vector<std::string> fv_names_new(fv_new.size());
    for (std::map<int,int>::iterator i=fv_new.begin(); i != fv_new.end(); ++i) {
      fva[(*i).second] = fv[(*i).first];
      fv_names_new[(*i).second] = fv_names[(*i).first];
    }
    fv = FloatVarArray(home, fva);
    fv_names = fv_names_new;
#endif
  }

  Printer::~Printer(void) { }

}}

// STATISTICS: flatzinc-any
