
#ifndef LOGIC_SIMPLIFICATIONS_
#define LOGIC_SIMPLIFICATIONS_  

#include "term.h"
#include "termoperators.h"

namespace logic
{

   namespace simplifications
   {
      term apply_normalize( const term& func, const term& arg );
          // Construct func( arg ) and beta-normalize the result.

      // pol counts negations, starting at 1. 
      // This means that ( pol & 1 ) means that the formula is positive.

      term subset_expansion( unsigned int pol, const term& s1, const term& s2 );
         //  Returns forall x : x in s1 -> x in s2,    or  
         //          exists x : x in s1 && ! x in s2.

      term separation_expansion
         ( unsigned int pol, const term& t, const term& set, const term& pred );
         // Expands t in { x in s | P(x) } into t in x and P(t),
         // and beta-normalizes the result. 
  
      term replacement_expansion
         ( unsigned int pol, const term& t, const term& dom, const term& func );
         // Expands t in repl( dom, f ) into 
         // exists z:Set  z in dom and t = f(z), and
         // beta-normalizes the result.  

      term union_expansion( unsigned int pol, const term& t, const term& u );
         // Returns exists z:Set   z in t and t in u.

      term unique_expansion( unsigned int pol, const term& pred, const term& t );
         // Returns pred(t) && forall z : Set   P(z) -> z = t.
 
      struct logical
      {
         logical( ) = default; 
         term operator( ) ( const term& t, size_t depth ) const;

         void print( std::ostream& out ) const
            { out << "(simplification::logical)"; }
      };

      struct settheoretic
      {
         settheoretic( ) = default;

         term operator( ) ( const term& t, size_t depth ) const; 

         void print( std::ostream& out ) const
            { out << "(simplification::settheoretic)"; }
      };

      term topnorm( term t );
   }

} 

#endif


