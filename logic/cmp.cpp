
#include "cmp.h"
#include "inspections.h"

logic::cmp::weight_t logic::cmp::weight( const type& tp )
{

   switch( tp. sel( )) 
   {
   case type_form:
   case type_obj:
      return 1;
   case type_struct:
      return 1;
   case type_unchecked:
      return 1; 
   case type_func:
      {
         auto f = tp. view_func( ); 
         size_t w = weight( f. result( ));
         for( size_t i = 0; i != f. size( ); ++ i )
            w += weight( f. arg(i));
         return w + 1; 
      }
   }

   std::cout << "the selector is " << tp. sel( ) << "\n";
   throw std::logic_error( "wrong selector in type" );  
}

namespace logic::cmp
{
   namespace 
   {
      struct counter
      {
         weight_t val;

         counter( ) noexcept : val(0) 
            { }

         void operator( ) ( const term& tm, size_t vardepth ) 
         { 
            if( tm. option_is_lambda( ))
            {
               val += tm. view_lambda( ). size( ); 
               return;  
            }

            if( tm. option_is_quant( ))
            {
               val += tm. view_quant( ). size( );
               return;
            }

            val += 1;
         }
      };
   }
}

logic::cmp::weight_t logic::cmp::weight( const term& t ) 
{
   counter cnt;

   count( cnt, t, 0 );
   return cnt. val; 
}


bool logic::cmp::equal( const type& tp1, const type& tp2 ) 
{
   if( tp1. sel( ) != tp2. sel( ))
      return false;
 
   switch( tp1. sel()) 
   {
   case type_form:
   case type_obj:
      return true;

   case type_struct:
      {
         exact s1 = tp1. view_struct( ). def( );
         exact s2 = tp2. view_struct( ). def( );
         return s1 == s2;
      } 
  
   case type_unchecked:
      { 
         identifier id1 = tp1. view_unchecked( ). id( );
         identifier id2 = tp2. view_unchecked( ). id( ); 
         return id1 == id2;
      }

   case logic::type_func:
      {
         auto func1 = tp1. view_func( );
         auto func2 = tp2. view_func( );

         if( !equal( func1. result( ), func2. result( )) )
            return false;

         if( func1. size( ) != func2. size( )) 
            return false;

         for( size_t i = 0; i < func1. size( ); ++i ) 
         {
            if( !equal( func1. arg(i), func2. arg(i)) )
               return false;
         }

         return true;
      }

   default:
      std::cout << "the selector is " << tp1. sel( ) << "\n";
      throw std::logic_error("unknown selector in equal()");
   }
}


bool
logic::cmp::equal( const term& t1, const term& t2 ) 
{

   if( t1. sel( ) != t2. sel( ))
      return false;

   switch( t1.sel( )) 
   {
   case op_exact:
      return t1.view_exact( ).ex( ) == t2.view_exact( ).ex( );

   case op_debruijn:
      return t1.view_debruijn( ).index( ) == t2.view_debruijn( ). index( ); 

   case op_unchecked:
      return t1.view_unchecked( ).id( ) == t2.view_unchecked( ).id( );

   case op_false:
   case op_error:
   case op_true:
      return true;

   case op_not:
   case op_prop:
      return cmp::equal( t1.view_unary( ).sub( ), t2.view_unary( ).sub( ));

   case op_and: 
   case op_or:
   case op_implies:
   case op_equiv:
   case op_lazy_and:
   case op_lazy_or:
   case op_lazy_implies:
   case op_equals:
      {
         auto bin1 = t1. view_binary( );
         auto bin2 = t2. view_binary( );
         if( !cmp::equal( bin1.sub1( ), bin2.sub1( )))
            return false;
         return cmp::equal( bin1.sub2( ), bin2.sub2( ));
      } 

   case op_kleene_and:
   case op_kleene_or:
      {
         auto kl1 = t1. view_kleene( );
         auto kl2 = t2. view_kleene( );

         if( kl1. size( ) != kl2. size( ))
            return false;

         for( size_t i = 0; i != kl1. size( ); ++ i )
         {
            if( !equal( kl1.sub(i), kl2.sub(i)) )
               return false;
         }
         return true;
      }
 
   case op_forall:
   case op_exists:
   case op_kleene_forall:
   case op_kleene_exists:
      {
         auto quant1 = t1. view_quant( );
         auto quant2 = t2. view_quant( );

         if( quant1. size( ) != quant2. size( ))
            return false;

         for( size_t i = 0; i != quant1. size( ); ++ i )
         {
            if( !equal( quant1.var(i).tp, quant2.var(i).tp ))
               return false;
         }

         return equal( quant1. body( ), quant2. body( ));
      }

   case op_let:
      {
         auto let1 = t1. view_let( );
         auto let2 = t2. view_let( );

         if( !equal( let1.var( ).tp, let2.var( ).tp ))
            return false;
         if( !equal( let1.val( ), let2.val( )))
            return false;
         return  equal( let1.body( ), let2.body( ));
      }

   case op_apply: 
      {
         auto ap1 = t1. view_apply( );
         auto ap2 = t2. view_apply( );

         if( ap1. size( ) != ap2. size( ))
            return false; 

         for( size_t i = 0; i != ap1. size( ); ++ i )
         {
            if( !equal( ap1.arg(i), ap2.arg(i)) )
               return false;
         }

         return equal( ap1.func( ), ap2.func( ));
      } 

   case op_lambda:
      {
         auto lamb1 = t1. view_lambda( );
         auto lamb2 = t2. view_lambda( );

         if( lamb1. size( ) != lamb2. size( ))
            return false;

         for( size_t i = 0; i != lamb1. size( ); ++ i )
         {
            if( !equal( lamb1.var(i).tp, lamb2.var(i).tp ))
               return false;
         }

         return equal( lamb1.body( ), lamb2.body( ));
      }

   }

   std::cout << t1. sel( ) << "\n";
   throw std::logic_error( "equal: operator not implemented" ); 
}


