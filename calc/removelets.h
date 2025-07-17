
#ifndef CALC_REMOVELETS_
#define CALC_REMOVELETS_

// Remove let operators by taking the definition out of the term,
// and putting it in the beliefstate.

#include "logic/beliefstate.h"
#include "logic/context.h"

#include "namegenerator.h"

namespace calc
{

   logic::term
   removelets( logic::beliefstate& blfs, namegenerator& gen,
               logic::context& ctxt, logic::term f );
      // Replace lets by global definitions.
      // Since lets are rare, we try to reuse as much as possible. 
      // We cannot handle Kleene operators.

}

#endif

