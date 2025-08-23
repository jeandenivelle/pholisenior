
#ifndef CALC_SEQUENT_
#define CALC_SEQUENT_

#include <string_view>
#include <optional>

#include "errorstack.h"

#include "extension.h"
#include "logic/beliefstate.h"
#include "namegenerator.h"

namespace calc
{

   // Sequent is not a complete class. It is more like a view
   // into a beliefstate.

   struct sequent
   {
      logic::beliefstate& blfs; 
      namegenerator gen;

      std::vector< extension > steps;
         // The extensions.

      std::vector< size_t > blockings;
         // These are indices into steps.

      sequent( logic::beliefstate& blfs ) noexcept
         : blfs( blfs )
      { } 

      logic::exact assume( std::string_view namebase, const logic::term& frm );
      logic::exact assume( std::string_view namebase, const logic::type& tp );
      logic::exact define( std::string_view namebase, const logic::term& val,
                           const logic::type& tp );

      size_t size( ) const { return steps. size( ); } 
      void restore( size_t s ); 

      void ugly( std::ostream& out ) const;      
      void pretty( std::ostream& out, bool showblocked = false ) const;

      identifier get_fresh_ident( std::string namebase );

      std::optional< logic::term >
      getformula( logic::exact ex, errorstack& err ) const;
         // We should separate this function into isformula( ) and getformula.
    
      logic::exact getexactname( size_t i ) const;  
         // Get the exact name used. 
   };

   inline std::ostream& operator << ( std::ostream& out, const sequent& seq )
   {
      seq. pretty( out );
      return out;
   }
}

#endif

