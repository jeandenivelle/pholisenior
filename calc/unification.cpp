
#include "unification.h"
#include "logic/inspections.h"
#include "logic/replacements.h"

std::ostream& calc::operator << ( std::ostream& out, const forallstarts& univ )
{
   out << "Start of Foralls:\n";
   for( const auto& u : univ )
      out << "   " << u. first << ": " << u. second << "\n";
   return out;
}


std::optional< calc::varorig >
calc::assignable( const unifsubst& subst, const forallstarts& univ,
                  const termorig& t, size_t vardepth )
{
   if( t.tm.sel( ) != logic::op_debruijn )
      return { };

   size_t ind = t.tm.view_debruijn( ). index( );

   // Local variable -> not assignable!

   if( ind < vardepth )
      return { };

   ind -= vardepth;

   // Existential variable -> not assignable!

   if( ind < univ. at( t. orig ))
      return { };

   ind -= univ. at( t. orig );

   return varorig( ind, t. orig );
}


bool 
calc::unify( unifsubst& subst, const forallstarts& univ, 
             const termorig& t1, size_t vardepth1,
             const termorig& t2, size_t vardepth2 )
{
   std::cout << "Unifying\n";
   std::cout << subst << "\n";
   std::cout << "   " << t1 << " [" << vardepth1 << " / ";
   std::cout << "univ:" << univ. at( t1. orig ) << "]\n";
   std::cout << "   " << t2 << " [" << vardepth2 << " / ";
   std::cout << "univ:" << univ. at( t2. orig ) << "]\n";
   std::cout << "\n";

   // If one side is a DeBruijn index, we look it up in subst.

   auto asn1 = assignable( subst, univ, t1, vardepth1 );
   if( asn1 )
   {
      auto p = subst. find( asn1. value( )); 
      if( p != subst. end( )) 
         return unify( subst, univ, p -> second, 0, t2, vardepth2 );
   }

   auto asn2 = assignable( subst, univ, t2, vardepth2 );
   if( asn2 )
   {
      auto p = subst. find( asn2. value( ));
      if( p != subst. end( )) 
         return unify( subst, univ, t1, vardepth1, p -> second, 0 );
   }

   // If both sides are assignable variables, and equal,
   // we return true:

   if( asn1 && asn2 )
   {
      varorig::equal_to eq;
      if( eq( asn1. value( ), asn2. value( )) )
         return true;
   }

   // If the left is assignable, we try to do the assignment:

   if( asn1 )
   {
      // If right term contains a local variable, we cannot assign:

      if( logic::nearest_debruijn( t2.tm, vardepth2 ) < vardepth2 )
         return false;

      // If left variable occurs in right term, we cannot assign:

      if( occurs( subst, univ, asn1. value( ), t2, vardepth2 ))
         return false;
 
      subst. push( asn1. value( ), 
                   termorig( sink( t2.tm, vardepth2 ), t2. orig ));

      return true;
   }

   if( auto asn2 = assignable( subst, univ, t2, vardepth2 ); asn2 )
   {
      std::cout << "right assignable " << asn2. value( ) << "\n";
      
      throw std::logic_error( "finish it" );
   }

   // In the remaining case, t1 and t2 must be structurally equal:

   if( t1.tm.sel( ) != t2.tm.sel( ))
      return false;

   switch( t1.tm.sel( ))
   {
   case logic::op_debruijn:
      {
         // Assignable cases have been checked before.
         // We check only existential and local.

         auto ind1 = t1.tm.view_debruijn( ). index( );
         auto ind2 = t2.tm.view_debruijn( ). index( );

         if( ind1 < vardepth1 || ind2 < vardepth2 )
         {
            // Either of them is local.
            // They must both be local and equal. 

            if( ind1 >= vardepth1 || ind2 >= vardepth2 )
               return false;

            // Origin does not matter for local variables.

            return ind1 == ind2;  
         }

         ind1 -= vardepth1;
         ind2 -= vardepth2;

         // If either of them is existential, they must be exactly
         // equal, also the origins.

         if( ind1 < univ. at( t1. orig ) || 
             ind2 < univ. at( t2. orig ))
         {
            std::cout << "existential\n";
            std::cout << "   " << ind1 << " " << t1. orig << "\n";
            std::cout << "   " << ind2 << " " << t2. orig << "\n";

            return ind1 == ind2 && t1.orig == t2.orig; 
         } 

         throw std::logic_error( "I think this is unreachable" );
      }

   case logic::op_exact:
      {
         auto ex1 = t1.tm.view_exact( );
         auto ex2 = t2.tm.view_exact( );
         return ex1. ex( ) == ex2. ex( );
      }

   case logic::op_unchecked:
      throw std::logic_error( "unchecked identifier: Not handled" );
 
   case logic::op_apply:
      {
         auto ap1 = t1.tm.view_apply( );
         auto ap2 = t2.tm.view_apply( );

         if( ap1. size( ) != ap2. size( ))
            return false;

         auto b = unify( subst, univ,
                     termorig( ap1.func( ), t1. orig ), vardepth1,
                     termorig( ap2.func( ), t2. orig ), vardepth2 );
         {
            if(!b) return false;  
         } 

         for( size_t i = 0; i != ap1. size( ); ++ i )
         {
            auto b = unify( subst, univ,
                        { ap1.arg(i), t1.orig }, vardepth1,
                        { ap2.arg(i), t2.orig }, vardepth2 );
            
            if(!b) return false;
         }

         return true;
      }
   } 
   
}


bool 
calc::occurs( const unifsubst& subst, const forallstarts& univ, 
              varorig var, const termorig& tt, size_t vardepth )
{
   std::cout << "checking occurrence of " << var << " in " << tt; 
   std::cout << " [" << vardepth << "]\n";

   // SUBSTITUTIONS ARE NOT LOOKED UP

   if( auto asn = assignable( subst, univ, tt, vardepth ); asn )
   {
      // If equal, then occurs:

      varorig::equal_to eq;
      return eq( var, asn. value( ));
   }

   switch( tt.tm.sel( ))
   {
   case logic::op_debruijn:
      return false;  // Left is assignable, we checked for right. 
   case logic::op_unchecked:
   case logic::op_false:
   case logic::op_error:
   case logic::op_true:
      return false;

   }

   std::cout << tt.tm.sel( ) << "\n";
   throw std::logic_error( "occurs check: not implemented" ); 
}


