
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

   void
   checkandresolve( beliefstate& everything, errorstack& err );
      // Structurally check the beliefs.
      // The beliefstate is not const, because we resolve overloads.

   void uncheck( type& tp );
   void uncheck( term& t );
      // Make a term t unchecked.

   exact::unordered_set allexact( const term& t );
      // Get the exact names in t.


   // Technically seen, we should return std::optional< T > ,
   // where T is some unit type. 
   // This is because a structural type by itself can have only one type.
   // This is a bit overdone, so we just use bool.

   bool
   checkandresolve( const beliefstate& blfs, errorstack& errors, 
                    type& tp );
    
   std::optional< type > 
   checkandresolve( const beliefstate& blfs, errorstack& errors,
                    context& ctxt, term& t );
      // We check and resolve the overloads. We don't care about
      // dependencies. Dependencies are checked by a separate
      // function. 
   
   std::optional< type >
   try_apply( type ftype, const std::vector< type > & argtypes, size_t pos );
      // Try to apply ftype on argtypes[ pos ... ].

   std::optional< type >
   try_apply( const beliefstate& blfs, exact name, 
              const std::vector< type > & argtypes, size_t pos ); 
}

#endif


