
#include <vector>

#include "logic/exact.h"
#include "logic/term.h"

namespace calc
{
   struct proofstate
   {
      logic::exact name; 
         // Name of the goal (theorem or assumption)

      unsigned int prop; 
         // 0 if we are trying to refute !prop( goal ). 
         // 1 if we are trying to refute !goal.

      std::vector< logic::exact > defs;
         // Definitions are in principle permanent,
         // but we could also delete them. 

      logic::term goal;
         // Negated goal in ANF. Using the paper terminology, it is in
         // alt^exists_6. 

      size_t disj;
         // Chosen disjunct in goal.

      std::vector< logic::exact > exist; 
         // These are declarations of the existentially quantified
         // variables in the goal. 


   };

}

   
