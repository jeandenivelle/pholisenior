
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

            // We need to lift, but we don't lift over 0:

            if( vardepth == 0 )
               return p -> second;
            else
            {
               bool c = false;
               return topdown( lifter( vardepth ), p -> second, 0, c );
            }
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


#if 0
logic::term
logic::contextsubst::operator( ) ( term t, size_t vardepth,
                                   bool& change ) const
{
   std::cout << "contextsubst " << t << " [" << vardepth << "]\n";

   if( t. sel( ) == op_debruijn ) 
   {
      size_t ind = t. view_debruijn( ). index( ); 
      if( ind >= vardepth )
      {
         // id -= vardepth;  
         if( ind >= nrvars ) throw std::logic_error( "contextsubst: wrong De Bruijn" ); 
         ind = nrvars - ind - 1;
         std::cout << "absolute = " << ind << "\n";

         if( vect. size( ) && ind <= vect. back( ). first )
         {
            size_t i0 = 0;
            size_t i1 = vect. size( );
            while( i1 - i0 > 1 )
            {
               size_t mid = i0 + ( i1 - i0 ) / 2;
               if( ind < vect[ mid ]. first )
                  i1 = mid;
               else
                  i0 = mid; 
            }

            if( i0 >= vect. size( )) 
               throw std::logic_error( "cannot happen I think" );
                  // We checked before that the vector is not empty.

            if( vect[i0]. first == ind )
            {
               change = true;
               bool c = false;
               return topdown( lifter( vardepth ), vect[i0]. second, 0, c );
         }
         }
      }
      else
         std::cout << "dont even bother for " << ind << "\n";
   }
   return t;
}
#endif

#if 0
void logic::contextsubst::restore( size_t s )
{
   while( nrvars > s )
   {
      -- nrvars; 
      if( vect. size( ) && vect. back( ). first == nrvars )
         vect. pop_back( ); 
   }
}

void logic::contextsubst::print( std::ostream& out ) const
{
   out << "Contextsubst( nrvars = " << nrvars << " ):\n";
   for( const auto& v : vect )
      out << "   " << v. first << " := " << v. second << "\n";
}
#endif

#if 0

logic::term 
logic::betareduction::operator( ) ( const term& t, size_t vardepth ) const
{
   if ( t.sel( ) == sel_appl )
   {
      auto appl = t. view_appl( );
      auto f = appl. func( );

      if ( f.sel( ) == sel_lambda )
      {
         auto lamb = f. view_lambda( );
         auto body = lamb. body( );

         values val;
         for( size_t i = 0; i != appl. size( ); ++ i )
            val. push_back( appl. arg(i));
        
         if ( appl.size( ) != lamb. size( ) )
            throw std::runtime_error( "wrong number of arguments" );

         long unsigned int changes = 0;
         return topdown_sar( changes, val, std::move( body ), 0 );
      }
   }
   return t;
};

#endif

void
logic::betareduction::print( std::ostream& out ) const
{
  out << "(beta reduction)";
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
         return topdown_sar( changes, lift, eq. second, 0 );
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

logic::term
logic::definition::operator( ) ( const term& t, size_t vardepth ) const
{
   // std::cout << "definition in " << t << " / " << vardepth << "\n";

   if( t. sel( ) == sel_ident )
   {
      if( t. view_id( ). ident( ) == id )
      { 
         lifter lift( vardepth );
         long unsigned int changes = 0;
         return topdown_sar( changes, lift, val );
      }
   }
   return t;
}

void
logic::definition::print( std::ostream& out ) const
{
   out << "definition:\n";
   out << "   " << id << " := " << val << "\n";
}

#endif

