
// Written by Hans de Nivelle, Dec. 2024.

#ifndef LOGIC_COUNTING_
#define LOGIC_COUNTING_

#include "term.h"
#include <map>


namespace logic
{
   // The counter does not need to count. It can also
   // check presence. 

   template< typename F >
   concept counter = 
      requires( F f, term t, size_t d )
         { { f( t, d ) } -> std::same_as< void > ; };

   template< counter C >
   void count( C& counter, const term& t, size_t vardepth )
   {
      counter( t, vardepth );

      switch( t. sel( ))
      {
      case op_exact:
      case op_debruijn:
      case op_unchecked:
      case op_false:
      case op_error:
      case op_true:
         return;

      case op_not:
      case op_prop:
         {
            auto un = t. view_unary( );
            count( counter, un. sub( ), vardepth );
         }
         return;

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
            count( counter, bin. sub1( ), vardepth );
            count( counter, bin. sub2( ), vardepth );
         }
         return;

      case op_kleene_and:
      case op_kleene_or:
         {
            auto kl = t. view_kleene( );
            for( size_t i = 0; i != kl. size( ); ++ i )
               count( counter, kl. sub(i), vardepth );
         }
         return;

      case op_forall:
      case op_exists:
      case op_kleene_forall:
      case op_kleene_exists:
         {
            auto q = t. view_quant( ); 
            count( counter, q. body( ), vardepth + q. size( ));
         }
         return;

      case op_apply:
         {
            auto ap = t. view_apply( );
            count( counter, ap. func( ), vardepth );
            for( size_t i = 0; i != ap. size( ); ++ i )
               count( counter, ap. arg(i), vardepth );
         }
         return;
      }

      std::cout << "count: " << t. sel( ) << "\n";
      throw std::logic_error( "dont know how to count" );
   }


   struct debruijn_counter
   {
      std::map< size_t, size_t > occ;
         // It must be an ordered map. We use the debruijn counter 
         // to introduce a new predicate for a subformula, and we want 
         // the variables to be ordered in this predicate in the same 
         // order as they are quantified in the surrounding scope. 

      void operator( ) ( const term& t, size_t vardepth );

      debruijn_counter( ) = default;
      debruijn_counter( debruijn_counter&& ) = default;
      debruijn_counter& operator = ( debruijn_counter&& ) = default;
         // Blocking coincidental copying.

      size_t size( ) const { return occ. size( ); }
      using const_iterator = std::map< size_t, size_t > :: const_iterator;
      const_iterator begin( ) const { return occ. begin( ); }
      const_iterator end( ) const { return occ. end( ); }

      void print( std::ostream& out ) const;
   };

   inline debruijn_counter count_debruijn( const term& t )
   {
      debruijn_counter db;
      count( db, t, 0 );
      return db;
   }


   exact::unordered_map< size_t > count_beliefs( const term& t );

}


#endif

