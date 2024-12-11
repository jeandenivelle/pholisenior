
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

   const char* getcstring( selector val );
   attractions getattractions( selector sel );


   struct parprinter
   {
      std::ostream& out;
      unsigned int nr;
    
      parprinter( std::ostream& out ) noexcept 
         : out( out ), nr(0)
      { }

      parprinter( parprinter&& ) = default;
      parprinter& operator = ( parprinter&& );

      void printif( bool b ) 
      { 
         if(b) { out << "( "; ++ nr; } 
      }

      ~parprinter( )
      {
         while( nr -- )
            out << " )";
      }
   };

   void print( std::ostream& out, const beliefstate& blfs, 
               const type& tp, attractions attr );
 
   void print( std::ostream& out, const beliefstate& blfs,
               context& ctxt, uniquenamestack& names,
               const term& t, attractions attr );

   void print( std::ostream& out, const beliefstate& blfs,
               context& ctxt, const term& t, 
               attractions attr = attractions( ));

#if 0
   void print( std::ostream& out, const logic::term& tm,
               logic::context& ctxt, logic::proofstate& state, 
               uniquenamestack& names, attractions attr );

   void print( std::ostream& out, const logic::term& tm,
               logic::context& ctxt, logic::proofstate& state,
               attractions attr = attractions( ));
#endif

   void addnames( const logic::context& ctxt, uniquenamestack& names );

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

