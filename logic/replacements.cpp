
// Written by Hans de Nivelle, September 2022
// Made additions in April 2023.

#include "replacements.h"
#include "kbo.h"


logic::term 
logic::lifter::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      auto db = t. view_debruijn( );
      if( size_t ind = db. index( ); ind >= vardepth )
      {
         change = true;
         return term( op_debruijn, ind + dist );
      }
   }
   return t; 
}

void 
logic::lifter::print( std::ostream& out ) const
{
   out << "lifter(" << dist << ")";
}


logic::term
logic::sinker::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      auto db = t. view_debruijn( );
      size_t ind = db. index( );
      if( ind >= vardepth )
      {
         ind -= vardepth; 
         if( ind < dist )
            throw std::logic_error( "sinker. DeBruijn index too small" );

         change = true;
         return term( op_debruijn, ind - dist );
      }  
   }     
   return t; 
}
   
void
logic::sinker::print( std::ostream& out ) const
{
   out << "sinker(" << dist << ")";
}


logic::term logic::lift( term tm, size_t dist )
{
   if( dist == 0 )
      return tm;
   else
      return outermost( lifter( dist ), std::move( tm ), 0 );
}

logic::term logic::sink( term tm, size_t dist )
{
   if( dist == 0 )
      return tm;
   else
      return outermost( sinker( dist ), std::move( tm ), 0 );
}

 
logic::term
logic::sparse_subst::operator( ) ( term t, size_t vardepth, 
                                   bool& change ) const
{
   // std::cout << "sparse-subst " << t << " [" << vardepth << "]\n";

   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         ind -= vardepth;
         auto p = repl. find( ind );
         if( p != repl. end( ))
         {
            change = true;
            return lift( p -> second, vardepth );
         }
      }
   }

   return t;
}


void logic::sparse_subst::print( std::ostream& out ) const
{
   out << "Sparse subst:\n";
   for( const auto& r : repl )
      out << "   #" << r. first << " := " << r. second << "\n";
}

logic::term
logic::singlesubst::operator( ) ( term t, size_t vardepth, 
                                  bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         change = true;

         if( ind == vardepth )
            return lift( value, vardepth );
         else
            return term( op_debruijn, ind - 1 );
      }
   }
   return t;
}

void logic::singlesubst::print( std::ostream& out ) const
{
   out << "singlesubst( #0 := " << value << " )";
}


logic::term
logic::fullsubst::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn ) 
   {
      size_t ind = t. view_debruijn( ). index( ); 
      if( ind >= vardepth )
      {
         change = true; 

         if( ind < vardepth + values. size( ))
         {
            ind -= vardepth; 
            ind = values. size( ) - ind - 1;   // Because we look backwards.

            return lift( values[ ind ], vardepth );
         }
         else
         {
            ind -= values. size( );
            return term( op_debruijn, ind );
         }   
      }
   }
   return t;
}

void logic::fullsubst::print( std::ostream& out ) const
{
   out << "Full Substitution:\n";
   for( auto i = 1 - (ssize_t) values. size( ); const auto& t: values )
   {
      out << "   #" << i << " := " << t << "\n";
      ++ i;
   }
}

logic::term
logic::argsubst::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         change = true;

         if( ind < vardepth + arity )
         {
            ind -= vardepth;
            ind = arity - ind - 1;   // Because we look backwards.

            return lift( argterm. view_apply( ). arg( ind ), vardepth );
         }
         else
         {
            ind -= arity;
            return term( op_debruijn, ind );
         }
      }
   }
   return t;
}

void logic::argsubst::print( std::ostream& out ) const
{
   out << "Argument Substitution:\n";
   std::cout << arity << "\n";
   for( size_t i = 0; i < arity; ++ i )
   {
      out << "   #" << (ssize_t)(1 + i) - (ssize_t)arity << " := ";
      out << argterm. view_apply( ). arg(i) << "\n";
   }
}

logic::term 
logic::betareduction::operator( ) ( term t, size_t vardepth, bool& change ) 
{
   if( t. sel( ) == op_apply )
   {
      auto appl = t. view_apply( );
      auto f = appl. func( );

      if( f. sel( ) == op_lambda )
      {
         auto lamb = f. view_lambda( );
         auto body = lamb. body( );

         if( lamb. size( ) > appl. size( ))
         {
            throw std::logic_error( 
                          "not enough arguments in lambda-application" );
         }

         argsubst subst( t, lamb. size( ));
         auto res = outermost( subst, lamb. extr_body( ), 0 );

         change = true;
         ++ counter;

         // If too many arguments were given, we construct
         // an application term with the remaining arguments:

         if( lamb. size( ) < appl. size( ))
         {
            res = term( op_apply, res, std::initializer_list< term > ( ));
            for( size_t i = lamb. size( ); i != appl. size( ); ++ i )
               res. view_apply( ). push_back( appl. arg(i)); 
         }
         
         return res;
      }
   }
   return t;
};


void logic::betareduction::print( std::ostream& out ) const
{
  out << "betareduction(" << counter << ")";
}


#if 0

namespace logic
{
   namespace
   {
      bool equal( const term& t1, lifter lift1,
                  const term& t2, lifter lift2, size_t vardepth )
      {
#if 0
         std::cout << t1 << " / " << lift1 << " == ";
         std::cout << t2 << " / " << lift2 << " ?\n"; 
#endif

         if( t1. sel( ) != t2. sel( ) )
            return false;

         switch( t1. sel( ) )
         {
         case sel_debruijn:
            {
               auto p1 = t1. view_debruijn( );
               auto p2 = t2. view_debruijn( );

               size_t ind1 = p1. index( );
               if( ind1 >= vardepth ) 
                  ind1 += lift1. dist; 

               size_t ind2 = p2. index( ); 
               if( ind2 >= vardepth )
                  ind2 += lift2. dist; 

               return ind1 == ind2; 
            }

         case sel_ident:
            {
               normident::equal_to eq;
               return eq( t1. view_id( ). ident( ), t2. view_id( ). ident( ));
            }
         
         case sel_false:
         case sel_true:
         case sel_emptyset:
         case sel_infset:
            return true;

         case sel_not:
         case sel_union:
         case sel_pow:
         case sel_unique:
            {
               auto v1 = t1. view_unary( );
               auto v2 = t2. view_unary( );  
               return equal( v1. sub( ), lift1, v2. sub( ), lift2, vardepth );
            }

         case sel_and:
         case sel_or:
         case sel_implies:
         case sel_equiv: 
         case sel_equals: 
         case sel_in:
         case sel_subset:
         case sel_insert:
         case sel_sep:
         case sel_repl:
            {
               auto v1 = t1. view_binary( );
               auto v2 = t2. view_binary( );

               if( !equal( v1. sub1( ), lift1, v2. sub1( ), lift2, vardepth ))
                  return false;
               if( !equal( v1. sub2( ), lift1, v2. sub2( ), lift2, vardepth ))
                  return false;

               return true;
            }
         case sel_forall:
         case sel_exists:
            {
               auto v1 = t1. view_quant( );
               auto v2 = t2. view_quant( ); 

               if( !is_eq( kbo::topleftright( v1. var( ). tp, v2. var( ). tp )))
                  return false;
 
               return equal( v1. body( ), lift1, v2. body( ), lift2, 
                             vardepth + 1 );
            }

         case sel_appl:
            {
               auto v1 = t1. view_appl( );
               auto v2 = t2. view_appl( );

               if( v1. size( ) != v2. size( ))
                  return false; 

               if( !equal( v1. func( ), lift1, v2. func( ), lift2, vardepth ))
                  return false;
               
               for( size_t i = 0; i < v1. size( ); ++i )
               {
                  if( !equal( v1. arg(i), lift1, v2. arg(i), lift2, vardepth ))
                     return false;
               }
               return true;
            }

         case sel_lambda:
            {
               auto v1 = t1. view_lambda( );
               auto v2 = t2. view_lambda( );

               if( v1. size( ) != v2. size( ) )
                  return false;

               for( size_t i = 0; i != v1. size( ); ++ i )
               {
                  if( !is_eq( 
                         kbo::topleftright( v1. var(i). tp, v2. var(i). tp )))
                  {
                     return false;
                  }
               }

               return equal( v1. body( ), lift1, v2. body( ), lift2, 
                             vardepth + v1. size( ));
            }
         }
         
         std::cout << "equal " << t1. sel( ) << " case not implemented\n";
         throw std::logic_error( "stop" );
      }
   }
}


logic::term
logic::equalitysystem::operator( ) ( const term& t, size_t vardepth ) const
{
   for( const auto& eq : sys )
   {
      if( equal( eq. first, lifter( vardepth ), t, lifter(0), 0 ))
      {
         lifter lift( vardepth );
         long unsigned int changes = 0;
         return outermost_sar( changes, lift, eq. second, 0 );
      }
   }

   return t;
}

void
logic::equalitysystem::print( std::ostream& out ) const
{
   out << "equality system:\n";
   for( const auto& eq : sys )
      out << "   " << eq. first << " --> " << eq. second << "\n";
}

#endif

