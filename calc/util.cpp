
#include "util.h"
#include "logic/inspections.h"
#include "logic/replacements.h"


logic::term
calc::quantify( logic::selector op, const logic::context& ctxt,
                const logic::term& body )
{
   if( ctxt. size( ) == 0 )
      return body;
   else
   {
      auto res = logic::term( op, body,
                              std::initializer_list< logic::vartype > ( ));
      auto q = res. view_quant( );

      // We need to do in reverse order, because context looks back:

      for( size_t i = ctxt. size( ); i -- ; )
         q. push_back( logic::vartype( ctxt. getname(i), ctxt. gettype(i) ));
      return res;
   }
}

std::pair< logic::debruijn_counter, logic::term > 
calc::norm_debruijns( logic::term ff )
{
   if constexpr( false )
   {
      std::cout << "normalizing:\n\n";
      std::cout << "   " << ff << "\n";
   }

   auto freevars = count_debruijn( ff );
      // In increasing order. That means that the
      // nearest De Bruijn variable is first.

   // The normalizing substitution replaces the variables
   // in f by #0,#1,#2, ...

   logic::sparse_subst norm;
   size_t var = 0;
   for( const auto& f : freevars )
   {
      norm. assign( f. first, logic::term( logic::op_debruijn, var ));
      ++ var;
   }

   std::cout << "normalizer = " << norm << "\n";

   bool change = false;
   ff = topdown( norm, std::move(ff), 0, change );

   return std::pair( std::move( freevars ), std::move( ff ));
}

logic::context
calc::restriction( const logic::context& ctxt, 
                   const logic::debruijn_counter& used )
{
   // context look back from the end. Because of that, the
   // highest De Bruijn variable comes first in the context.

   logic::context res; 
   for( auto it = used. end( ); it != used. begin( ); )
   {
      -- it;
      size_t vv = it -> first;
      res. append( ctxt. getname(vv), ctxt. gettype(vv) ); 
   }

   return res;
}

logic::term
calc::application( const logic::term& f, 
                   const logic::debruijn_counter& vars )
{
   auto res = logic::term( logic::op_apply, f,
                           std::initializer_list< logic::term > ( ));

   auto view = res. view_apply( );

   // We need to go in reverse order, because we want the
   // type of the furthest De Bruijn variable first:

   for( auto it = vars. end( ); it != vars. begin( ); )
   {
      -- it;
      size_t vv = it -> first;
      view. push_back( logic::term( logic::op_debruijn, vv ));
   }

   return res;
}

