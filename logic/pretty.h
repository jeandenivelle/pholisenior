
// Everything related to pretty printing. 
// Written by Akhmetzhan Kussainov 
// and Hans de Nivelle.
// May 2023.

#ifndef LOGIC_PRETTY_
#define LOGIC_PRETTY_

#include <iostream>
#include "logic/term.h"
#include "logic/context.h"
#include "logic/beliefstate.h"
#include "logic/proofstate.h"
#include "logic/error.h"

#include "uniquenamestack.h"

namespace logic { 
namespace pretty 
{

   struct attractions
   {
      unsigned int left;
      unsigned int right;
         // Higher number means : more attraction. Zero means:
         // No. attraction. at. all. Not. even. the. slighest.

      attractions( ) noexcept 
         : left(0), right(0) 
      { }

      attractions( unsigned int left, unsigned int right )
         : left( left ), right( right )
      { }

      void print( std::ostream& out ) const
         { out << left << '/' << right; } 
   };

   attractions getattractions( selector sel );

   void print( std::ostream& out, const beliefstate& blfs,
               context& ctxt, uniquenamestack& names,
               const term& t, attractions attr );

   void print( std::ostream& out, const beliefstate& blfs,
               context& ctxt, const term& t, 
               attractions attr = attractions( ));

   void print( std::ostream& out, const logic::term& tm,
               logic::context& ctxt, logic::proofstate& state, 
               uniquenamestack& names, attractions attr );

   void print( std::ostream& out, const logic::term& tm,
               logic::context& ctxt, logic::proofstate& state,
               attractions attr = attractions( ));

   uniquenamestack 
   getnames( const logic::context& ctxt, size_t ss );

   inline uniquenamestack
   getnames( const logic::context& ctxt )
   {
      return getnames( ctxt, ctxt. size( ));
   }

   void print( std::ostream& out, 
               uniquenamestack& names, const logic::belief& );

   uniquenamestack
   print( std::ostream& out, const logic::context& cxt ); 
      // Because one frequently prints a context together with
      // a term in this context, it is necessary to know the 
      // uniquenamestack that was created while printing the context.

   void print( std::ostream& out, const logic::beliefstate& );

   void print( std::ostream& out, 
               uniquenamestack& , const logic::error& err );

}}

#endif

