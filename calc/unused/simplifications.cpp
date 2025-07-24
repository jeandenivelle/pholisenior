
#include <iostream>
#include "simplifications.h"
#include "normalization.h"
#include "replacements.h"
#include "kbo.h"

logic::term
logic::simplifications::apply_normalize( const term& func, const term& arg )
{
   if( func. sel( ) != sel_lambda )
      return term( sel_appl, func, { arg } );
   else
   {
      auto lam = func. view_lambda( );
      if( lam. size( ) != 1 )
         throw std::runtime_error( "apply_normalize : lambda of wrong arity" ); 

      substitution subst( arg );
      betareduction beta;

      return normalize_sar( beta, topdown( subst, lam. body( )));
   }
}


logic::term 
logic::simplifications::subset_expansion( unsigned int pol, 
                                          const term& s1, const term& s2 )
{
   std::cout << "subset " << s1 << " " << s2 << "\n";

   if( pol & 1 )
      return forall( { "z", sel_set }, 
                implies( in( 0_db, s1 + 1 ), in( 0_db, s2 + 1 )) ); 
   else
      return exists( { "z", sel_set },
                in( 0_db, s1 + 1 ) && !in( 0_db, s2 + 1 ) );
}

logic::term
logic::simplifications::separation_expansion
   ( unsigned int pol, const term& t, const term& set, const term& pred )
{
   if( pol & 1 )
      return in( t, set ) && apply_normalize( pred, t );
   else
      return !in( t, set ) || ! apply_normalize( pred, t );
}


logic::term
logic::simplifications::replacement_expansion
   ( unsigned int pol, const term& t, const term& dom, const term& func )
{
   betareduction beta;

   auto t1 = t + 1;
   auto dom1 = dom + 1;
   auto func1z = apply_normalize( func + 1, 0_db );

   if( pol & 1 )
      return exists( { "z", type( sel_set ) }, 
                     in( 0_db, dom1 ) && t1 == func1z );
   else
      return forall( { "z", type( sel_set ) }, 
                     ! in( 0_db, dom1 ) || ! ( t1 == func1z ));
}


logic::term
logic::simplifications::unique_expansion
   ( unsigned int pol, const term& pred, const term& t )
{
   std::cout << "pred = " << pred << "\n";
   std::cout << "t = " << t << "\n";

   if( pol & 1 )
      return apply_normalize( pred, t ) &&
             forall( { "z", type( sel_set ) },
                     implies( apply_normalize( pred + 1, 0_db ),
                              0_db == ( t + 1 )));
   else
      return !apply_normalize( pred, t ) ||
             exists( { "z", type( sel_set ) },
                     apply_normalize( pred + 1, 0_db ) && 
                              0_db != ( t + 1 ));
}


logic::term
logic::simplifications::union_expansion( unsigned int pol, const term& t, const term& u )
{
   auto t1 = t + 1;
   auto u1 = u + 1;

   if( pol & 1 )
      return exists( { "z", type( sel_set ) }, 
                     in( t1, 0_db ) && in( 0_db, u1 )); 
   else
      return forall( { "z", type( sel_set ) },
                     !in( t1, 0_db ) || !in( 0_db, u1 ));
}


logic::term 
logic::simplifications::logical::operator( ) ( const term& t, 
                                               size_t depth ) const
{
   unsigned int pol = 1;
   term body = t;

   while( body. sel( ) == sel_not )
   {
      body = body. view_unary( ). sub( );
      ++ pol;
   }

   switch( body. sel( ))
   {
   case sel_false:
      if( !(pol & 1 ))
         return term( sel_true );
      break;

   case sel_true:
      if( !(pol & 1 ))
         return term( sel_false );
      break;

   case sel_and:
      if( !( pol & 1 ))
      {
         auto p = body. view_binary( );
         return !p. sub1( ) || !p. sub2( );
      }
      break; 

   case sel_or:
      if( !( pol & 1 ))
      {
         auto p = body. view_binary( );
         return !p. sub1( ) && !p. sub2( );
      }
      break;

   case sel_implies:
      {
         auto p = body. view_binary( ); 
         if( pol & 1 )
            return ! p. sub1( ) || p. sub2( ); 
         else
            return p. sub1( ) && ! p. sub2( ); 
      }
      break; 

   case sel_equiv:
      {
         auto p = body. view_binary( );
         if( pol & 1 )
            return implies( p. sub1( ), p. sub2( )) &&
                   implies( p. sub2( ), p. sub1( )); 
         else
            return ( p. sub1( ) || p. sub2( )) &&
                   ( !p. sub1( ) || !p. sub2( ));
      }
      break;

   case sel_equals:
      {
         auto p = body. view_binary( );
         auto ord = kbo::compare( p. sub1( ), p. sub2( ));

         if( is_eq( ord ))
         {
            if( pol & 1 )
               return term( sel_true );
            else 
               return term( sel_false ); 
         }
      }
      break;

   case sel_forall:
      {
         if( !( pol & 1 ))
         {
            auto p = body. view_quant( ); 
            return exists( p. var( ), ! p. body( ));
         }
      } 
      break;

   case sel_exists:
      {
         if( !( pol & 1 ))
         {
            auto p = body. view_quant( );
            return forall( p. var( ), ! p. body( )); 
         }
      }
      break; 
   }

   // We are going to return t with double negations removed,
   // while trying to preserve very-equality as much as possible:

   if( pol == 1 || pol == 2 )
      return t;

   if( pol & 1 )
      return body;
   else
      return !body;
}


logic::term
logic::simplifications::settheoretic::operator( ) ( const term& t,
                                                    size_t depth ) const
{
   unsigned int pol = 1;
   term body = t;

   while( body. sel( ) == sel_not )
   {
      body = body. view_unary( ). sub( );
      ++ pol; 
   }

   if( body. sel( ) == sel_in )
   {
      auto el = body. view_binary( ); 

      if( el. sub2( ). sel( ) == sel_emptyset )
      {
         if( pol & 1 )
            return term( sel_false );
         else
            return term( sel_true );
      }

      if( el. sub2( ). sel( ) == sel_insert ) 
      {
         auto sub = el. sub2( ). view_binary( ); 

         if( pol & 1 )
            return ( el. sub1( ) == sub. sub1( )) || 
                   in( el. sub1( ), sub. sub2( ));
         else
            return !( el. sub1( ) == sub. sub1( )) && 
                   ! in( el. sub1( ), sub. sub2( )); 
      }  

      if( el. sub2( ). sel( ) == sel_pow )
      {
         auto sub = el. sub2( ). view_unary( ); 
         return subset_expansion( pol, el. sub1( ), sub. sub( ));
      }
   
      if( el. sub2( ). sel( ) == sel_sep )
      {
         auto sep = el. sub2( ). view_binary( );
         return separation_expansion( pol, el. sub1( ), 
                                      sep. sub1(), sep. sub2()); 
      }

      if( el. sub2( ). sel( ) == sel_repl )
      {
         auto repl = el. sub2( ). view_binary( );
         return replacement_expansion( pol, el. sub1( ), 
                                       repl. sub1( ), repl. sub2( )); 
      }

      if( el. sub2( ). sel( ) == sel_union )
      {
         auto un = el. sub2( ). view_unary( );
         return union_expansion( pol, el. sub1( ), un. sub( ));
      }
   }

   if( body. sel( ) == sel_subset )
   {
      auto sub = body. view_binary( );
      return subset_expansion( pol, sub. sub1( ), sub. sub2( ));
   }

   // It works in both cases, with unique to the right, or unique to the left: 

   if( body. sel( ) == sel_equals )
   {
      auto eq = body. view_binary( );
      if( eq. sub2( ). sel( ) == sel_unique )
      {
         auto u = eq. sub2( ). view_unary( ); 
         return unique_expansion( pol, u. sub( ), eq. sub1( ));
      }

      if( eq. sub1( ). sel( ) == sel_unique )
      {
         auto u = eq. sub1( ). view_unary( );
         return unique_expansion( pol, u. sub( ), eq. sub2( ));
      }
   } 

   // We are going to return t with double negations removed,
   // but we try to preserve very-equality as much as possible.

   if( pol == 1 || pol == 2 )
      return t;

   if( pol & 1 )
      return body;
   else
      return !body;
}

auto logic::simplifications::topnorm( term t )
   -> term 
{
   settheoretic set;
   logical log;

   // std::cout << "-----before simpl: " << t << "\n";

   t = set( std::move(t), 0 );
   t = log( std::move(t), 0 );

   // std::cout << "-----after simpl: " << t << "\n";
   return t;
}


