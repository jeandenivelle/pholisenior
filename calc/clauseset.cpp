
#include "clauseset.h"
#include "logic/cmp.h"

bool 
calc::contains( const logic::term& lit, const logic::term& form, size_t skip )
{
   if( !form. option_is_kleene( ))
      throw std::logic_error( "calc::contains: Not a Kleene operator" ); 

   auto kl = form. view_kleene( );
   for( size_t i = 0; i != kl. size( ); ++ i )
   {
      if( i != skip && equal( lit, kl. sub(i)) )
         return true;
   } 
   return false;
}

bool 
calc::subset( const logic::term& form1, size_t skip1,
              const logic::term& form2, size_t skip2 )
{
   if( !form1. option_is_kleene( ))
      throw std::logic_error( "calc::subset: Not a Kleene operator" );

   if( form1. sel( ) != form2. sel( ))
      throw std::logic_error( "calc::subset: Operators differ" );

   auto kl1 = form1. view_kleene( );
   for( size_t i = 0; i != kl1. size( ); ++ i )
   {
      if( i != skip1 && !contains( kl1. sub(i), form2, skip2 ))
         return false;
   }
   return true; 
}

logic::term
calc::merge( const logic::term& form1, size_t skip1,
             const logic::term& form2, size_t skip2 )
{
   if( !form1. option_is_kleene( ))
      throw std::logic_error( "calc::merge: Not a Kleene operator" );

   if( form1. sel( ) != form2. sel( ))
      throw std::logic_error( "calc::merge: Operators differ" );

   auto res = 
      logic::term( form1. sel( ), std::initializer_list< logic::term > ( ));

   auto kl = res. view_kleene( ); 

   auto kl1 = form1. view_kleene( );
   for( size_t i = 0; i != kl1. size( ); ++ i )
   {
      if( i != skip1 && !contains( kl1. sub(i), res, kl. size( ) ))
         kl. push_back( kl1. sub(i));
   }

   auto kl2 = form2. view_kleene( );
   for( size_t i = 0; i != kl2. size( ); ++ i )
   {
      if( i != skip2 && !contains( kl2. sub(i), res, kl. size( ) ))
         kl. push_back( kl2. sub(i));
   }

   return res;      
}


