
#ifndef RESO_POLARITY_
#define RESO_POLARITY_

#include <iostream>
#include "logic/term.h"

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

   logic::term apply( polarity pol, const logic::term& t ); 
}

#endif

