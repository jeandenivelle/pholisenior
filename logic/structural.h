
// Written by Hans de Nivelle, Dec. 2024.
// Everything related to structural type checking.

#ifndef LOGIC_STRUCTURAL_
#define LOGIC_STRUCTURAL_

#include <iostream>
#include <optional>

#include "errorstack.h"
#include "term.h"
#include "beliefstate.h"
#include "context.h"

namespace logic
{

#if 0
   error_report 
   checkstructure( nameranking& rk, beliefstate& everything );
      // Structurally check the beliefs and rank the identifiers. 
      // The beliefstate is not const, because we resolve
      // overloads. 

#endif

   void uncheck( term& t );
      // Make term t unchecked.

   exact::unordered_set allexact( const term& t );
      // Get the exact names in t.


   // Technically seen, we should return std::optional< unit > ,
   // because a metatype by itself can have only one type.
   // This is a bit overdone, so we just use bool.

   bool
   checkandresolve( const beliefstate& blfs, errorstack& err,
                    context& ctxt, type& tp );
    
   std::optional< type > 
   checkandresolve( const beliefstate& blfs, errorstack& err,
                    context& ctxt, term& t );
      // We check and resolve the overloads. We don't care about
      // dependencies. Dependencies are checked by a separate
      // function. 
}

#endif


