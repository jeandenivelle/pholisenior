
#ifndef RESO_TRANSFORMATIONS_
#define RESO_TRANSFORMATIONS_

#include "logic/term.h"
#include "logic/beliefstate.h"
#include "logic/context.h"

#include "namegenerator.h"
#include "polarity.h"

namespace reso
{

   bool biggerthan( const logic::term& t, size_t max );
      // Return true if term t is bigger than max.
      // We stop checking when we reach max, so that this function works
      // in constant time.

   logic::term 
   nnf( logic::beliefstate& blfs, namegenerator& gen,
        logic::context& ctxt, 
        logic::term f, const polarity pol, const unsigned int eq );

      // Variable eq is the number of equivalences that we are in.
      // If it becomes too high, we introduce a definition, because
      // an equivalence generates a positive and a negative copy.
      // Introduces Kleene operators at the same time,
      // and add definitions. 

   logic::term flatten( logic::term f );

   // Create a definition for the formula:

   logic::term
   definesubform( logic::beliefstate& blfs, namegenerator& gen,
                  logic::context& ctxt, logic::term t );

   logic::term
   clausify( logic::beliefstate& blfs, namegenerator& gen,
             logic::context& ctxt, logic::term& f, unsigned int alt );
      // Term f must have Kleene operations only, and in NNF.
      // Even level means and/forall.
      // Odd level means or/exists.

}

#endif

