
#ifndef CALC_SEQUENT_
#define CALC_SEQUENT_

#include <initializer_list>
#include <string_view>

#include "extension.h"
#include "logic/beliefstate.h"
#include "namegenerator.h"

namespace calc
{

   // It is not a complete class. It is more like a view
   // into a beliefstate.

   struct sequent
   {
      logic::beliefstate& blfs; 
      logic::exact goal; 
      std::vector< extension > ext;
         // The extensions.

      namegenerator gen;

      sequent( logic::beliefstate& blfs, logic::exact goal )
         : blfs( blfs ), goal( goal ) 
      { } 
         // Must be a theorem or an assumption.

      void apply_initial( std::string_view namebase );
         // Extend with the initial formula.

      void ugly( std::ostream& out ) const;      
      void pretty( std::ostream& out ) const;

      void
      addformula( std::string_view namebase, const logic::term& f,
                  unsigned int par1, unsigned int par2,
                  unsigned int br, unsigned int nr );
         // Add a comment parameter !

      identifier fresh_ident( std::string_view namebase );

   };

   inline std::ostream& operator << ( std::ostream& out, const sequent& seq )
   {
      seq. pretty( out );
      return out;
   }
}

#endif

