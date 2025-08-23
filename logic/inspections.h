
// Written by Hans de Nivelle, Dec. 2024.

#ifndef LOGIC_INSPECTIONS_
#define LOGIC_INSPECTIONS_

#include "term.h"
#include <map>

namespace logic
{

   // A counter does not need to count. It can also
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

      case op_lambda:
         {
            auto lam = t. view_lambda( );
            count( counter, lam. body( ), vardepth + lam. size( ));
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
         // order as they were quantified in the surrounding scope. 

      void operator( ) ( const term& t, size_t vardepth );

      debruijn_counter( ) = default;
      debruijn_counter( debruijn_counter&& ) = default;
      debruijn_counter& operator = ( debruijn_counter&& ) = default;
         // Blocking accidental copying.

      size_t size( ) const { return occ. size( ); }
      using const_iterator = 
            std::map< size_t, size_t > :: const_iterator;

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


   // Can be used for finding the nearest De Bruijn index. 

   struct debruijn_cmp 
   {
      size_t nearest; 

      void operator( ) ( const term& t, size_t vardepth );

      debruijn_cmp( ) = delete;

      debruijn_cmp( size_t upperbound ) noexcept
         : nearest( upperbound ) 
      { } 

      void print( std::ostream& out ) const;
   };

   inline size_t 
   nearest_debruijn( const term& t, size_t upperbound )
   {
      auto near = debruijn_cmp( upperbound );
      count( near, t, 0 );
      return near. nearest;
   }


   struct exactcounter
   {
      exact::unordered_map< size_t > occ;
      bool extending;
         // If extending == true, we insert exact names that are not in
         // occ yet.

      explicit exactcounter( bool extending ) noexcept
         : extending( extending )
      { }

      void addtodomain( exact ex )
         { occ. insert( std::pair< exact, size_t > ( ex, 0 )); }
            // add ex to the domain, with zero occurrences.
            // This is not needed if extending == true. 

      void operator( ) ( const term& t, size_t vardepth );

      size_t at( exact ex ) 
         { return occ. at( ex ); }

      void print( std::ostream& out ) const; 
   };

}

#endif

