
#ifndef CALC_UTIL_
#define CALC_UTIL_

#include "logic/context.h"
#include "logic/term.h"

namespace calc
{
  
   bool isatom( const logic::term& f );
   bool isliteral( const logic::term& f );

   // We won't create a quantifier if ctxt is empty:

   logic::term
   quantify( logic::selector op, const logic::context& ctxt,
             const logic::term& body );
  
}

#endif

