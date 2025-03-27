
// Written by Hans de Nivelle, Sept 2022 
// Rewritten Dec. 2024. I changed the interface
// to use only SAR, and I adapted it for PHOLI.

#ifndef LOGIC_TOPDOWN_
#define LOGIC_TOPDOWN_    

#include <iostream>

namespace logic
{

   template< typename F >
   concept replacement =
      requires( F f, term t, size_t d, bool& c )
         { { f( t, d, c ) } -> std::same_as< term > ; };

      // I would like to enforce that c is a reference, but that  
      // seems not possible.

   // topdown means that we try to rewrite the top level of t, before
   // we try to rewrite subterms of t.
   // If we can rewrite at the top level, we don't look at the subterms 
   // any more.

   template< replacement R > 
   term topdown( const R& repl, term t, size_t vardepth, bool& change ) 
   {
      // std::cout << "entering topdown " << t << "\n";

      {
         bool c = false;
         t = repl( std::move(t), vardepth, c );
         if(c)
         {
            change = true;
            return t;
         }
      }

      switch( t. sel() )
      {
      case op_exact:
      case op_debruijn:
      case op_unchecked:
      case op_false:
      case op_error:
      case op_true:  
         return t; 

      case op_not:
      case op_prop:
         {
            auto p = t. view_unary( );
            p. update_sub( 
                    topdown( repl, p. extr_sub( ), vardepth, change ));
         }
         return t;

      case op_and:
      case op_or:
      case op_implies:
      case op_equiv:
      case op_lazy_and:
      case op_lazy_or:
      case op_lazy_implies:
      case op_equals:
         {
            auto bin = t. view_binary( );
            bin. update_sub1( 
                      topdown( repl, bin. extr_sub1( ), vardepth, change ));
            bin. update_sub2(
                      topdown( repl, bin. extr_sub2( ), vardepth, change ));
         }
         return t;

      case op_kleene_and:
      case op_kleene_or:
         {
            auto kl = t. view_kleene( );
            for( size_t i = 0; i != kl. size( ); ++ i )
            {
               kl. update_sub( i,
                      topdown( repl, kl. extr_sub(i), vardepth, change ));
            }
         }
         return t;

      case op_forall:
      case op_exists:
      case op_kleene_forall:
      case op_kleene_exists: 
         {
            auto q = t. view_quant( ); 

            q. update_body( topdown( repl, q. extr_body( ), 
                                     vardepth + q. size( ), change ));
         }
         return t; 

      case op_apply:
         {
            auto ap = t. view_apply( );

            ap. update_func( topdown( repl, ap. extr_func( ), 
                             vardepth, change ));

            for( size_t i = 0; i != ap. size( ); ++ i )
            {
               ap. update_arg( i, topdown( repl, ap. extr_arg(i), 
                               vardepth, change ));
            }
         }
         return t;

      case op_lambda:
         {
            auto lam = t. view_lambda( ); 
            lam. update_body( topdown( repl, lam. extr_body( ), 
                              vardepth + lam. size( ), change )); 
         }
         return t;

      }

      std::cout << t. sel( ) << "\n";
      throw std::runtime_error( "topdown: case not implemented" );  
   }

}


#endif



