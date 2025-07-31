
#ifndef CALC_UNIFICATION_
#define CALC_UNIFICATION_

#include "indexedstack.h"
#include "logic/term.h"

namespace calc
{

   struct varorig
   {
      size_t var;  
      unsigned int orig; 

      varorig( size_t var, unsigned int orig )
         : var( var ), orig( orig )
      { }
     
      void print( std::ostream& out ) const
         { out << "#" << var << " @ " << orig; }

      struct hash
      {
         size_t operator( ) ( varorig v ) const
         {
            auto hv = v. var; 
            hv ^= ( v. orig << 3 );
            hv ^= ( v. orig << 5 );
            return hv;
         }
      };

      struct equal_to
      {
         bool operator( ) ( varorig v1, varorig v2 ) const
         {
            return v1. var == v2. var && v1. orig == v2. orig; 
         }
      };
   };

   struct termorig
   {
      const logic::term& tm;
      unsigned int orig;

      termorig( const logic::term& tm, unsigned int orig )
         : tm( tm ), orig( orig )
      { }

      termorig( const termorig& ) noexcept = default;

      void print( std::ostream& out ) const
         { out << tm << " @ " << orig; } 

   };

   using unifsubst = 
   indexedstack< varorig, termorig, varorig::hash, varorig::equal_to > ; 

   using normalizer =
   indexedstack< varorig, size_t, varorig::hash, varorig::equal_to > ;


   using universals = std::unordered_map< unsigned int, size_t > ;
      // For each origine, the point from where the variables are universal.
      // These can be assigned. Remember that DeBruijn indices
      // look backward.

   std::ostream& operator << ( std::ostream& out, const universals& univ );


   bool 
   unify( unifsubst& subst, const universals& univ, 
          termorig t1, size_t vardepth1,
          termorig t2, size_t vardepth2 );

      // Existential variables (DeBruijn indices) are treated like constants.
      // unifsubst has stack-like behaviour. In the case of failure,
      // stack may be still extended. 

   bool 
   unify( unifsubst& subst, const universals& univ, 
          varorig var1, size_t vardepth1,
          termorig t2, size_t vardepth2 );

   bool 
   occurs( const unifsubst& subst, 
           std::unordered_set< varorig, 
                       varorig::hash, varorig::equal_to > & checked, 
           varorig var, termorig t, size_t vardepth );
 
   bool occurs( const unifsubst& subst, varorig var, termorig t );
      // True if var occurs in tm. The infamous occurs check:
}

#endif

