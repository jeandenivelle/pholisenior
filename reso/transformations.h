
#ifndef RESO_TRANSFORMATIONS_
#define RESO_TRANSFORMATIONS_

#include "logic/term.h"
#include "logic/beliefstate.h"
#include "logic/context.h"

#include "namegenerator.h"

namespace reso
{
   enum polarity { pol_pos, pol_neg, pol_prop, pol_negprop };
      // One could replace this by two booleans, one for pos/neg,
      // and one for prop, but I think that a single enum is nicer.

   const char* getcstring( polarity pol );

   inline std::ostream& operator << ( std::ostream& out, polarity pol )
      { out << getcstring( pol ); return out; }

   polarity negate( polarity );  

   logic::selector demorgan( logic::selector sel, polarity pol );
      // Apply the De Morgan rule if polarity is pol_neg or pol_negprop.
      // This function works only for Kleene operators.

   bool toobig( const logic::term& t, size_t max );
      // Return true if term t is bigger than max.

   std::vector< size_t > freevars( const logic::term& t );
      // Counts the free variables in t. 


   logic::term 
   nnf( logic::beliefstate& blfs, namegenerator& gen,
        logic::context& ctxt, 
        logic::term f, const polarity pol, const unsigned int eq );

      // Variable eq the number of equivalences that we are in.
      // If it gets too many, we introduce a definition, because
      // an equivalence generates a positive and a negative copy.

   // Create a definition from the formula:

   logic::term
   define( logic::beliefstate& blfs, logic::context& ctxt,
           logic::term t, polarity pol );


}

#endif

