
#ifndef CALC_SPLITEQUIV_
#define CALC_SPLITEQUIV_

#include "polarity.h"
#include "transformer.h"

#include "logic/beliefstate.h"

namespace calc
{
   size_t size( const logic::term& f, size_t current, size_t limit );

   size_t size( const logic::term& f, size_t limit );
      // Returns the size of f, but never more than limit.
      // The point of this function is that we stop traversing
      // the term when the limit is reached.

   constexpr static unsigned int maxequivs = 1;
   static_assert( maxequivs >= 1 );
      // Should not be less than 1.

   // It is called 'splitequiv', and not 'remove equiv' because
   // it does not remove any equivalences. It just puts them into
   // subformulas.

   logic::term
   splitequiv( transformer& trans, logic::beliefstate& blfs,
               logic::context& ctxt, logic::term f, 
               unsigned int nrequiv );

}

#endif

