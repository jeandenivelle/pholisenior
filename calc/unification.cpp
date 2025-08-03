
#include "unification.h"

std::ostream& calc::operator << ( std::ostream& out, const forallstarts& univ )
{
   out << "Start of Foralls:\n";
   for( const auto& u : univ )
      out << "   " << u. first << ": " << u. second << "\n";
   return out;
}

calc::unifsubst::const_iterator
calc::lookup( const unifsubst& subst, const forallstarts& univ,
              varorig var, size_t vardepth )
{
   std::cout << "lookup " << var << " [" << vardepth << "]\n";

   // Locally bound variables are not looked up:

   if( var.ind < vardepth )
      return subst. end( ); 

   var.ind -= vardepth;

   // Existential variable? 

   if( var. ind < univ.at( var.orig ))
      return subst. end( );

   var.ind -= univ.at( var.orig );

   return subst. find( var );
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
   std::cout << "   " << t1 << " [" << vardepth1 << "/";
   std::cout << univ. at( t1. orig ) << "]\n";
   std::cout << "   " << t2 << " [" << vardepth2 << "/";
   std::cout << univ. at( t2. orig ) << "]\n";
   std::cout << "\n";

   // If one side is a DeBruijn index, we look up in subst and restart:

   if( t1.tm.sel( ) == logic::op_debruijn )
   {
      auto ind1 = t1.tm.view_debruijn( ). index( ); 
      auto p = lookup( subst, univ, varorig( ind1, t1.orig ), vardepth1 );
      if( p != subst. end( )) 
         return unify( subst, univ, p -> second, 0, t2, vardepth2 );
   }

   if( t2.tm.sel( ) == logic::op_debruijn )
   {
      auto ind2 = t2.tm.view_debruijn( ). index( );
      auto p = lookup( subst, univ, varorig( ind2, t2.orig ), vardepth2 );
      if( p != subst. end( )) 
         return unify( subst, univ, t1, vardepth1, p -> second, 0 );
   }

   // If either side is an assignable variable, we do the assignment: 

   if( auto asn1 = assignable( subst, univ, t1, vardepth1 ); asn1 )
   {
      std::cout << "assignable " << asn1. value( ) << "\n";

      
   }

   // In the remaining case, the terms must be structurally equal:

   if( t1.tm.sel( ) != t2.tm.sel( ))
      return false;

   switch( t1.tm.sel( ))
   {
   case logic::op_debruijn:
      {
         auto ind1 = t1.tm.view_debruijn( ). index( );
         auto ind2 = t2.tm.view_debruijn( ). index( );
         if( ind1 < vardepth1 || ind2 < vardepth2 )
         {
            // Either of them is local.
            // They must both be local and equal. 

            if( ind1 >= vardepth1 || ind2 >= vardepth2 )
               return false;

            // Origin does not matter, they are local.

            return ind1 == ind2;  
         }

         ind1 -= vardepth1;
         ind2 -= vardepth2;

         // If either of them is existential, they must be exactly
         // equal, also the origins.

         if( ind1 < univ. at( t1. orig ) || 
             ind2 < univ. at( t2. orig ))
         {
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

#if 0
bool  
calc::unify( unifsubst& subst, const universals& univ, 
             varorig var1, size_t vardepth1,
             termorig t2, size_t vardepth2 )
{
   std::cout << "var-unify\n";
   std::cout << "   " << var1 << " [ " << vardepth1 << " ]\n";
   std::cout << "   " << t2 << " [ " << vardepth2 << " ]\n";

   if( var1.var < vardepth1 )
   {
      // Local variables are not assignable. Unification succeeds
      // only if the other side is the same local variable.

      if( t2.tm.sel( ) != logic::op_debruijn )
         return false;

      auto index2 = t2.tm.view_debruijn( ). index( );
      return index2 < vardepth2 && var1.var == index2; 
   }
   
   var1.var -= vardepth1;
   if( var1. var < univ. at( var1. orig ))
   {
      std::cout << "variable is existential\n";

      // Existential variables cannot be assigned to. 
      // We accept only if the other side is the same existential 
      // variable from the same origine.

      if( t2.tm.sel( ) != logic::op_debruijn )
         return false;

      auto index2 = t2.tm.view_debruijn( ). index( );
      if( index2 < vardepth2 ) 
         return false;
      index2 -= vardepth2;
      return var1.var == index2 && var1.orig == t2.orig; 
   }

   std::cout << "variable can be assigned\n";

   // It is an assignable variable.
   // Check if it already has an assignment: 
  
   auto p = subst. find( var1 );
   if( p != subst. end( ))
   {
      std::cout << "variable already has value!\n";
      throw std::logic_error( "stopping" );
   }
   
   std::cout << "we need to check if right side contains local\n";

   if( occurs( subst, var1, t2 ))
   {
      if( t2.tm.sel( ) == logic::op_debruijn )
      { 
         // This means that var1 occurs, and t2 is a variable.
         // Hence, they are equal.

         return true;
      }
      else
         return false;   // Proper occurrence. We reject.

   }

   std::cout << "we do the assignment\n";
}
#endif


bool 
calc::occurs( const unifsubst& subst, 
              varorigset& checked,
              varorig wanted, const termorig& tt, size_t vardepth )
{
   std::cout << "occurs check " << wanted << " in " << tt << "\n";
   switch( tt.tm.sel( ))
   {

   case logic::op_debruijn:
      {
         size_t ind = tt.tm.view_debruijn( ). index( );
         std::cout << ind << "\n";
         if( ind < vardepth ) return false;
         ind -= vardepth;
         if( checked. insert( varorig( ind, tt.orig )). second )
         {
            // This means { ind, tt.orig } was inserted, which implies
            // that we didn't check it yet. 

            auto p = subst. find( varorig( ind, tt.orig ));
            if( p != subst. end( ))
               return occurs( subst, checked, wanted, p -> second, vardepth );
            else 
               return ind == wanted.ind && tt.orig == wanted.orig;
         }
         else
            return false; 
      }   
   }

   std::cout << tt.tm.sel( ) << "\n";
   throw std::logic_error( "occurs check: not implemented" ); 
}


bool calc::occurs( const unifsubst& subst, varorig var, const termorig& tt )
{
   std::unordered_set< varorig, varorig::hash, varorig::equal_to > checked;
   return occurs( subst, checked, var, tt, 0 );
}

