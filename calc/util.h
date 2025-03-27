
#ifndef CALC_UTIL_
#define CALC_UTIL_

#include "logic/context.h"
#include "logic/term.h"
#include "logic/inspections.h"

namespace calc
{
  
   bool isatom( const logic::term& f );
   bool isliteral( const logic::term& f );

   // We won't create a quantifier if ctxt is empty:

   logic::term
   quantify( logic::selector op, const logic::context& ctxt,
             const logic::term& body );

   std::pair< logic::debruijn_counter, logic::term >
   norm_debruijns( logic::term ff );

   logic::context 
   restriction( const logic::context& ctxt, 
             const logic::debruijn_counter& used ); 
      // Restrict of ctxt to the used variables. 

   logic::term
   application( const logic::term& f, 
                const logic::debruijn_counter& vars );
      // Apply f on the domain of vars, from far to near. 
}

#endif

