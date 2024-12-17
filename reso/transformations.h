
#include "logic/term.h"
#include "logic/beliefstate.h"
#include "logic/context.h"


namespace reso
{
   enum polarity { pol_pos, pol_neg, pol_prop, pol_negprop };

   const char* getcstring( polarity pol );

   inline std::ostream& operator << ( std::ostream& out, polarity pol )
      { out << getcstring( pol ); return out; }

   polarity negate( polarity );  
 
   // Create a definition from the formula:

   logic::term nnf( logic::beliefstate& blfs, logic::context& ctxt, 
                    logic::term f, polarity pol, unsigned int equivs );

      // We count the number of equivalences that we are in.
      // If it gets too big, we introduce a definition.

   logic::term
   define( logic::beliefstate& blfs, logic::context& ctxt,
           logic::term t, polarity pol );

}
     
