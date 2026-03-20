/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Guido Tack <tack@gecode.org>
 *
 *  Copyright:
 *     Guido Tack, 2012
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


#include <gecode/search/seq/rbs.hh>

#include "gecode/flatzinc.hh"

namespace Gecode { namespace Search { namespace Seq {

  bool
  RestartStop::stop(const Statistics& s, const Options& o) {
    // Stop if the fail limit for the engine says so
    if (s.fail > l) {
      e_stopped = true;
      m_stat.restart++;
      return true;
    }
    // Stop if the stop object for the meta engine says so
    if (m_stop.stop(m_stat+s,o)) {
      e_stopped = false;
      return true;
    }
    return false;
  }

  bool RBS::initNext(const MetaInfo& mi) {
    // Reset number of no-goods found
    e->nogoods().ng(0);
    const bool requiresRestart = master->master(mi);
    stop->m_stat.nogood += e->nogoods().ng();
    return requiresRestart;
  }

  bool RBS::slave(const MetaInfo& mi) {
    Space* slave = master;
    master = master->clone();
    const bool c = slave->slave(mi);
    e->reset(slave);
    return c;
  }

  bool RBS::doRestart() {
    if (!restart) {
      return true;
    }
    // std::cerr << "RBS: restarting" << std::endl;
    restart = false;
    const MetaInfo mi(stop->m_stat.restart, MetaInfo::RR_SOL, ++solutionsSinceLastRestart, e->statistics().fail, last, e->nogoods());
    const bool r = initNext(mi);
    const auto stat = master->status(stop->m_stat);
    if (stat == SS_FAILED) {
      stop->update(e->statistics());
      delete master;
      master = nullptr;
      e->reset(nullptr);
      return false;
    }
    if (r) {
      stop->update(e->statistics());
      complete = slave(mi);
      solutionsSinceLastRestart = 0;
      stop->m_stat.restart++;
    }
    return true;
  }


  Space*
  RBS::next(void) {
    if (!doRestart()) {
      return nullptr;
    }
    while (true) {
      Space* n = e->next();
      if (n != nullptr) {
        // The engine found a solution
        restart = true;
        last = std::shared_ptr<Space>(n->clone());
        return n;
      } else if (alwaysStops()) {
        return nullptr;
      } else if ( (!complete && !e->stopped()) ||
                  (e->stopped() && stop->e_stopped) ) {
        // The engine must perform a true restart
        // The number of the restart has been incremented in the stop object
        if (!complete && !e->stopped()) {
          stop->m_stat.restart++;
        }
        solutionsSinceLastRestart = 0;
        MetaInfo mi(stop->m_stat.restart, e->stopped() ? MetaInfo::RR_LIM : MetaInfo::RR_CMPL, solutionsSinceLastRestart,e->statistics().fail, last,e->nogoods());
        initNext(mi);
        unsigned long long int nl = ++(*co);
        stop->limit(e->statistics(), nl);
        const auto stat = master->status(stop->m_stat);
        if (stat == SS_FAILED) {
          return nullptr;
        }
        complete = slave(mi);
      } else {
        return nullptr;
      }
    }
    GECODE_NEVER;
    return nullptr;
  }

  Search::Statistics
  RBS::statistics(void) const {
    return stop->metastatistics()+e->statistics();
  }

  void
  RBS::constrain(const Space& b) {
    if (!best)
      throw NoBest("RBS::constrain");
    if (last != nullptr) {
      last->constrain(b);
      if (last->status() == SS_FAILED) {
        last = nullptr;
      } else {
        return;
      }
    }
    last = std::shared_ptr<Space>(b.clone());
    master->constrain(b);
    e->constrain(b);
  }

  bool
  RBS::stopped(void) const {
    /*
     * What might happen during parallel search is that the
     * engine has been stopped but the meta engine has not, so
     * the meta engine does not perform a restart. However the
     * invocation of next will do so and no restart will be
     * missed.
     */
    return e->stopped();
  }

  bool
  RBS::alwaysStops(void) const {
    return ((stop != nullptr) && stop->done()) || e->alwaysStops();
  }

  RBS::~RBS(void) {
    delete e;
    delete master;
    delete co;
    delete stop;
  }

}}}

// STATISTICS: search-seq
