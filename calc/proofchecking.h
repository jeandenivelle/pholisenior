
// Written by Hans de Nivelle, July/August 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include <string_view>

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"
#include "optform.h"


namespace calc
{
   errorstack::builder
   errorheader( const sequent& seq, std::string_view rule );

   void print( std::ostream& out, const sequent& seq, const logic::term& tm );
   void print( std::ostream& out, logic::selector op );

   bool operatorcorrect( logic::selector op, 
                         const logic::term& fm, const sequent& seq, 
                         std::string_view rule, errorstack& err ); 

   bool istautology( const logic::term& disj ); 
      // True if disj is (very obviously) a tautology.

   logic::term simplify( const logic::term& tm );
 
   std::optional< logic::term >
   deduce( const proofterm& prf, sequent& seq, errorstack& err );
      // In case of failure, we vent our frustration into err, and 
      // return nothing. As with type checking,
      // we may try to recover from these errors, and check
      // other parts of the proof. 
}

#endif

