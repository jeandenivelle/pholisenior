
#include "unification.h"

bool 
calc::unify( unifsubst& subst,
             apart< const logic::term* > t1, size_t exists1, size_t vardepth1,
             apart< const logic::term* > t2, size_t exists2, size_t vardepth2 )
{
   std::cout << "unifying " << *t1.t << " / " << t1.orig << "\n";
   std::cout << *t2.t << " / " << t2.orig << "\n";
   std::cout << subst << "\n";

restart:
   // If one side is a DeBruijn index, we look up in subst and restart:

   if( t1.t -> sel( ) == logic::op_debruijn )
   {
      auto i = t1.t -> view_debruijn( ).index( );
      auto p = subst. find( { i, t1.orig } ); 
   }
 
   if( t1.t -> sel( ) != t2.t -> sel( ))
   {
      // There are only a few cases that we accept 

   }

   switch( t1.t -> sel( ))
   {

   case logic::op_apply:
      {
         auto ap1 = t1.t -> view_apply( );
         auto ap2 = t2.t -> view_apply( );

         if( ap1. size( ) != ap2. size( ))
            return false;

         if( !unify( subst,
                     apart( &ap1.func( ), t1. orig ), exists1, vardepth1,
                     apart( &ap2.func( ), t2. orig ), exists2, vardepth2 ))
         {
            return false;
         } 

      }
   } 
   

}

