
#ifndef CALC_APART_
#define CALC_APART_

#include "util/print.h"
#include "logic/term.h"

namespace calc
{

   template< typename T >
   struct apart
   {
      T t; 
      unsigned int orig; 

      apart( const T& t, unsigned int orig )
         : t(t), orig( orig )
      { }
     
      void print( std::ostream& out ) const
         { out << "#" << t << "/" << orig; }

      struct hash
      {
         size_t operator( ) ( apart<T> cp ) const
         {
            std::hash<T> h; 
            auto hv = h( cp. t );
            hv ^= ( cp. orig << 3 );
            hv ^= ( cp. orig << 5 );
            return hv;
         }
      };

      struct equal_to
      {
         bool operator( ) ( apart< size_t > cp1, apart< size_t > cp2 ) const
         {
            std::equal_to<T> eq; 
            return eq( cp1.t, cp2.t ) && cp1. orig == cp2. orig; 
         }
      };
   };


   template< >
   inline void apart< int > :: print( std::ostream& out ) const
         { out << "#$$$" << t << "/" << orig; }


}

#endif

