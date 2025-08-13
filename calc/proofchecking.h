
// Written by Hans de Nivelle, July/August 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include <string_view>

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{
   errorstack::builder
   errorheader( const sequent& seq, std::string_view rule );

   void print( std::ostream& out, const sequent& seq, const logic::term& tm );
   void print( std::ostream& out, logic::selector op );

   bool operatorcorrect( logic::selector op, 
                         const logic::term& fm, const sequent& seq, 
                         std::string_view rule, errorstack& err ); 

   std::optional< logic::term >
   subform( const logic::term& fm, size_t i, const sequent& seq, 
            std::string_view rule, errorstack& err );
      // Get fm[i] if it exists.

   std::optional< logic::term >
   uniquesubform( const logic::term& fm, const sequent& seq,
                  std::string_view rule, errorstack& err );
      // fm must be a Kleene disjunction of arity 1. 
      // We get out its unique subformula.

   logic::term replace( logic::term fm, size_t i, const logic::term& val );
      // Assign fm[i] := val, fm must be a Kleene operator.
 
   logic::term remove( logic::term fm, size_t i );
      // Remove i-th subformula. fm must be a Kleene operator. 
      // We move the subformulas after i one position back.
      // We could also swap with the last, which would be more efficient
      // (constant time), but we want to preserve order as much as possible.

   bool iscontradiction( const logic::term& fm );
      // True if fm counts as contradition.

   logic::term normalize( const logic::beliefstate& blfs, logic::term tm );

   std::optional< logic::term >
   deduce( const proofterm& prf, sequent& seq, errorstack& err );
      // In case of error, we express our frustration into err, and 
      // return nothing. Like with type checking,
      // we may try to recover from these errors, and check
      // other parts of the proof. 
}

#endif

