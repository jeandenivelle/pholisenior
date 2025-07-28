
#ifndef CALC_APARTVAR_
#define CALC_APARTVAR_

#include "util/print.h"

namespace calc
{
   // An apartvar is a variable that has been named apart: 

   struct apartvar
   {
      size_t var;
      unsigned int src; 

      apartvar( size_t var, unsigned int src )
         : var( var ), src( src )
      { }
     
      void print( std::ostream& out ) const
         { out << "#" << var << "/" << src; }

      struct hash
      {
         size_t operator( ) ( apartvar cp ) const
         {
            auto hv = cp. var;
            hv ^= ( cp. src << 3 );
            hv ^= ( cp. src << 5 );
            return hv;
         }
      };

      struct equal_to
      {
         bool operator( ) ( apartvar cp1, apartvar cp2 ) const
         {
            return cp1. var == cp2. var && cp1. src == cp2. src; 
         }
      };

   };

}

#endif

