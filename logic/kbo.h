
// Written by Akhmetzhan Kussainov and Hans de Nivelle Spring 2023.
// Revised in August 2024 by Hans de Nivelle. 

#ifndef LOGIC_KBO_
#define LOGIC_KBO_ 

#include <compare>
#include "term.h"

namespace logic
{
   namespace kbo 
   {
      size_t weight( const type& tp );
      size_t weight( const term& t );
   
      std::strong_ordering topleftright( const type& tp1, const type& tp2 );

      std::strong_ordering topleftright( const term& t1, const term& t2 );
         // Simple comparison, first comparing top, after that subtrees
         // from left to right.

      // This is the KBO that should be used for directing equalities:
 
      inline std::strong_ordering compare( const term& t1, const term& t2 )
      {
         size_t w1 = weight( t1 );
         size_t w2 = weight( t2 );

         if( w1 < w2 ) return std::strong_ordering::less;
         if( w1 > w2 ) return std::strong_ordering::greater;

         return topleftright( t1, t2 );   
      }

      void print( std::strong_ordering ord, std::ostream& out ); 
   }
}

#endif

