
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
      std::vector< extension > steps;
         // The extensions.

      namegenerator gen;

      sequent( logic::beliefstate& blfs ) noexcept
         : blfs( blfs )
      { } 

      logic::exact add_initial( selector sel, std::string_view namebase,
                                logic::term goal );
         // Extend with an initial formula. The sel
         // must be extr_truth or ext_prop. We return
         // the given name. The goal should be not negated or propped.
         // We take care of that.  

      void ugly( std::ostream& out ) const;      
      void pretty( std::ostream& out, bool showhidden = false ) const;

      void
      addformula( std::string namebase, const logic::term& f,
                  unsigned int par1, unsigned int par2,
                  unsigned int br, unsigned int nr );
         // Add a comment parameter !

      identifier get_fresh_ident( std::string namebase );
   };

   inline std::ostream& operator << ( std::ostream& out, const sequent& seq )
   {
      seq. pretty( out );
      return out;
   }
}

#endif

