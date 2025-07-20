
#ifndef CALC_SEQUENT_
#define CALC_SEQUENT_

#include <string_view>

#include "errorstack.h"

#include "extension.h"
#include "logic/beliefstate.h"
#include "namegenerator.h"

namespace calc
{

   struct failure
   {
      failure( ) noexcept = default;

      void print( std::ostream& out ) const
      {
         out << "(failure)";
      }
   };


   // It is not a complete class. It is more like a view
   // into a beliefstate.

   struct sequent
   {
      logic::beliefstate& blfs; 
      errorstack& err; 

      namegenerator gen;

      std::vector< extension > steps;
         // The extensions.

      std::vector< size_t > blockings;
         // These are indices into steps.

      sequent( logic::beliefstate& blfs, errorstack& err ) noexcept
         : blfs( blfs ),
           err( err ) 
      { } 

      logic::exact push( std::string_view namebase, const logic::term& frm );
      logic::exact assume( std::string_view namebase, const logic::type& tp );
      logic::exact define( std::string_view namebase, const logic::term& val,
                           const logic::type& tp );

      void ugly( std::ostream& out ) const;      
      void pretty( std::ostream& out, bool showhidden = false ) const;

      identifier get_fresh_ident( std::string namebase );

      logic::term getformula( logic::exact ex );
         // Not const because we may create an error. 
   };

   inline std::ostream& operator << ( std::ostream& out, const sequent& seq )
   {
      seq. pretty( out );
      return out;
   }
}

#endif

