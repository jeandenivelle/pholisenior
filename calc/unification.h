
#ifndef CALC_UNIFICATION_
#define CALC_UNIFICATION_

#include <optional>

#include "indexedstack.h"
#include "logic/term.h"

namespace calc
{

   using forallstarts = std::unordered_map< int, size_t > ;
      // For each origine, the point from where the variables are universal.
      // These can be assigned. Remember that DeBruijn indices
      // always look backward.

   std::ostream& operator << ( std::ostream& out, const forallstarts& univ );


   struct varorig
   {
      size_t ind;  
      int orig; 

      varorig( size_t ind, int orig )
         : ind( ind ), orig( orig )
      { }

      void print( std::ostream& out ) const
         { out << "#" << ind << " @ " << orig; }

      struct hash
      {
         size_t operator( ) ( varorig v ) const
         {
            auto hv = v. ind; 
            hv ^= ( v. orig << 3 );
            hv ^= ( v. orig << 5 );
            return hv;
         }
      };

      struct equal_to
      {
         bool operator( ) ( varorig v1, varorig v2 ) const
         {
            return v1. ind == v2. ind && v1. orig == v2. orig; 
         }
      };
   };


   struct termorig
   {
      const logic::term& tm;
      int orig;

      termorig( const logic::term& tm, int orig )
         : tm( tm ), orig( orig )
      { }

      termorig( const termorig& ) noexcept = default;

      void print( std::ostream& out ) const
         { out << tm << " @ " << orig; } 
   };


   using unifsubst = 
   indexedstack< varorig, termorig, varorig::hash, varorig::equal_to > ; 
      // We only assign universal variables, so the first universal
      // variable is always #0. In the values, existential variables
      // are possible.

   std::optional<varorig> 
   assignable( const unifsubst& subst, const forallstarts& univ,
               const termorig& t, size_t vardepth );

   unifsubst::const_iterator
   lookup( const unifsubst& subst, const forallstarts& univ, 
           varorig var1, size_t vardepth );

   bool 
   unify( unifsubst& subst, const forallstarts& univ, 
          const termorig& t1, size_t vardepth1,
          const termorig& t2, size_t vardepth2 );

      // Existential variables (DeBruijn indices) are treated like constants.
      // unifsubst has stack-like behaviour. In the case of failure,
      // stack may be still extended. 

   using varorigset =
   std::unordered_set< varorig,
                       varorig::hash, varorig::equal_to > ;

   bool 
   occurs( const unifsubst& subst, varorigset& checked,
           varorig var, const termorig& tt, size_t vardepth );
      // checked are those variables whose expansion we are sure does
      // not contain tm.  

   bool occurs( const unifsubst& subst, varorig var, const termorig& tt );
      // True if var occurs in tm. The infamous occurs check.
      // MAKE A DECISION ABOUT EXISTENTIAL QUANTIFIERS.
      // range of subst still contains existential variables.

   using normalizer =
   indexedstack< varorig, size_t, varorig::hash, varorig::equal_to > ;
}

#endif

