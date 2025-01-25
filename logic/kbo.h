
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
      using weight_t = uint_least64_t; 

      weight_t weight( const type& tp );
      weight_t weight( const term& t );
   
      std::strong_ordering topleftright( const type& tp1, const type& tp2 );

      std::strong_ordering topleftright( const term& t1, const term& t2 );
         // Simple comparison, first comparing top, after that subtrees
         // from left to right.

      // This is the KBO that should be used for directing equalities:
 
      inline std::strong_ordering compare( const term& t1, const term& t2 )
      {
         weight_t w1 = weight( t1 );
         weight_t w2 = weight( t2 );

         if( w1 < w2 ) return std::strong_ordering::less;
         if( w1 > w2 ) return std::strong_ordering::greater;

         return topleftright( t1, t2 );   
      }

      void print( std::strong_ordering ord, std::ostream& out ); 
   }

   inline bool equal( const logic::type& tp1, const logic::type& tp2 )
      { return is_eq( logic::kbo::topleftright( tp1, tp2 )); }

}

#endif

