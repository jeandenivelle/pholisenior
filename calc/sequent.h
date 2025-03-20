
#ifndef CALC_SEQUENT_
#define CALC_SEQUENT_

// Written by Hans de Nivelle, March 2025.

#include <vector>

#include "logic/exact.h"
#include "logic/term.h"

namespace calc
{

   struct formref 
   {
      std::vector< logic::exact > hiding;
         // Formulas that we are hiding.
      size_t hidden;
         // Number of times that we are hidden.

      logic::exact name; 
   };

   struct branch
   {
      logic::exact parent;
         // formula that we are a branch of.
         // (Must be a disjunction in ANF).

      size_t nr; 
        // Branch chosen in parent. 

      std::vector< logic::exact > localnames;
         // Assumptions.

      std::vector< formref > formulas;

   };

   struct sequent
   {
      logic::exact goalname; 
         // Name of the original goal (theorem or assumption)

      std::vector< logic::exact > defs;
         // Definitions are in principle permanent,
         // but we could also delete them later if
         // we are tired of them.

   };

}

#endif

