

// Remove let operators by taking the definition out of the term,
// and putting it in the beliefstate.
// This function works on arbitrary typechecked formulas.

#include "namegenerator.h"
#include "logic/beliefstate.h"
#include "logic/context.h"
#include "logic/replacements.h"

namespace trans
{

   logic::term
   removelets( logic::beliefstate& blfs, namegenerator& gen,
               logic::context& ctxt, logic::contextsubst& defs, 
               logic::term f );

}


