
#include "unification.h"

std::ostream& calc::operator << ( std::ostream& out, const universals& univ )
{
   out << "Universals:\n";
   for( const auto& u : univ )
      out << "   " << u. first << ": " << u. second << "\n";
   return out;
}


bool 
calc::unify( unifsubst& subst, const universals& univ, 
             termorig t1, size_t vardepth1,
             termorig t2, size_t vardepth2 )
{
   std::cout << "Unifying\n";
   std::cout << subst << "\n";
   std::cout << univ << "\n";
   std::cout << "   " << t1 << " [ " << vardepth1 << " ]\n";
   std::cout << "   " << t2 << " [ " << vardepth2 << " ]\n";

   // If one side is a DeBruijn index, we look up in subst and restart:

   if( t1.tm.sel( ) == logic::op_debruijn )
   {
      auto ind1 = t1.tm.view_debruijn( ). index( ); 
      return unify( subst, univ, 
                    varorig( ind1, t1.orig ), vardepth1, t2, vardepth2 );
   }

#if 0
   if( t1.tm.sel( ) == logic::op_debruijn )
   {
      auto ind = t1.tm.view_debruijn( ). index( );
      if( ind >= vardepth1 )
      {
         ind -= vardepth1;
         auto p = subst. find( varorig( ind, t1.orig )); 
         if( p != subst. end( ))
         {
            return unify( subst, termorig( p -> second ), exists1, 0,
                                 t2, exists2, vardepth2 );
         }
      } 
   }

   if( t2.tm.sel( ) == logic::op_debruijn )
   {
      auto ind = t2.tm.view_debruijn( ). index( );
      ind -= vardepth2;
      auto p = subst. find( varorig( ind, t2.orig ));
      if( p != subst. end( ))
      {
         return unify( subst, termorig( p -> second ), exists2, 0,
                              t1, exists1, vardepth1 );
      }
   }

   if( t1.tm.sel( ) == logic::op_debruijn )
      return unify_var( subst, 5,6,7 );

   if( t2.tm.sel( ) == logic::op_debruijn )
      return 100;

   if( t1.tm.sel( ) != t2.tm.sel( ))
      return false;
#endif
   switch( t1.tm.sel( ))
   {
   case logic::op_debruijn:
      {
         std::cout << "DeBruijn is very hard\n";
         auto ind1 = t1.tm.view_debruijn( ). index( );
         auto ind2 = t2.tm.view_debruijn( ). index( );
         if( ind1 < vardepth1 || ind2 < vardepth2 )
         {
            // Either of them is local.
            // They must both be local, and equal. 

            if( ind1 >= vardepth1 || ind2 >= vardepth2 )
               return false;

            // Origin does not matter, they are local.

            return ind1 == ind2;  
         }

         ind1 -= vardepth1;
         ind2 -= vardepth2;
 
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
      // only if other side is the same local variable.

      if( t2.tm.sel( ) != logic::op_debruijn )
         return false;

      auto index2 = t2.tm.view_debruijn( ). index( );
      return index2 < vardepth2 && var1.var == index2; 
   }
   
   var1.var -= vardepth1;
   if( var1. var < univ. at( var1. orig ))
   {
      std::cout << "variable is existential\n";

      // Existential variables are not assingeable.
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
      std::cout << "variable has value!\n";
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

bool 
calc::occurs( const unifsubst& subst, 
              std::unordered_set< varorig, 
                       varorig::hash, varorig::equal_to > & checked,
              varorig wanted, termorig t, size_t vardepth )
{
   std::cout << "occurs check " << wanted << " in " << t << "\n";
   switch( t.tm.sel( ))
   {

   case logic::op_debruijn:
      {
         size_t ind = t.tm.view_debruijn( ). index( );
         std::cout << ind << "\n";
         if( ind < vardepth ) return false;
         ind -= vardepth;
         if( checked. insert( varorig( ind, t.orig )). second )
         {
            // This means that we didn't check { ind, t.orig } yet.

            auto p = subst. find( varorig( ind, t.orig ));
            if( p != subst. end( ))
               return occurs( subst, checked, wanted, p -> second, vardepth );
            else 
               return ind == wanted.var && t.orig == wanted.orig;
         }
         else
            return false; 
      }   
      
   }

   std::cout << t.tm.sel( ) << "\n";
   throw std::logic_error( "occurs check: not implemented" ); 
}

bool calc::occurs( const unifsubst& subst, varorig var, termorig t )
{
   std::unordered_set< varorig, varorig::hash, varorig::equal_to > checked;
   return occurs( subst, checked, var, t, 0 );
}

