
#ifndef CALC_EXPANDER_
#define CALC_EXPANDER_

#include "errorstack.h"
#include "logic/beliefstate.h"

namespace calc
{

   struct expander
   {
      const identifier id;
      size_t i;
      size_t repl;   // Will be replaced.
 
      const logic::beliefstate& blfs; 
      errorstack& err; 

      expander( identifier id, size_t repl, 
                const logic::beliefstate& blfs, errorstack& err ) noexcept
         : id( id ), i(0), repl( repl ),
           blfs( blfs ),
           err( err )
      { } 

      logic::term 
      operator( ) ( logic::term tm, size_t vardepth, bool& change );
      
      void print( std::ostream& out ) const;
   }; 

}

#endif


