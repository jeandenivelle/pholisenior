
#include "transformer.h"
#include "kleening.h"
#include "splitequiv.h"
#include "alternating.h"

#include "logic/inspections.h"
#include "logic/replacements.h"

const char* calc::getcstring( transstep step )
{
   switch( step ) 
   {
   case step_cls:
      return "cls";
   case step_anf:
      return "anf"; 
   case step_kleening:
      return "kleening";
   case step_splitequiv:
      return "splitequiv";
   case step_rmlet:
      return "rmlet";
   case step_none:
      return "none";
   default:
      return "???"; 
   }
}

void calc::subformula::print( std::ostream& out ) const
{
   out << pred << "/" << pol << "      = " << form << "   ";
   out << "[" << last << "]"; 

}

bool calc::operator < ( const subformula& sub1, const subformula& sub2 )
{
   if( sub1. last < sub2. last )
      return true;
   if( sub1. last == sub2. last && sub1. nr < sub2. nr ) 
      return true;

   return false;
}

void 
calc::transformer::push( logic::exact pred,
                         logic::term form, polarity pol, transstep last )
{
   forms. push_back( subformula( pred, std::move( form ), 
                                 pol, last, nr ++ ));
   push_heap( forms. begin( ), forms. end( ));
}  

calc::subformula calc::transformer::extract_top( )
{
   auto tp = std::move( forms. front( ));
   pop_heap( forms. begin( ), forms. end( ));
   forms. pop_back( );
   return tp;
}

identifier
calc::transformer::fresh_ident( const logic::beliefstate& blfs,
                                const char* namebase )
{
   auto res = identifier( ) + gen. create( namebase );

   while( !blfs. getfunctions( res ). empty( ) ||
          !blfs. getstructdefs( res ). empty( ) ||
          !blfs. getformulas( res ). empty( ))
   {
      res = identifier( ) + gen. create( namebase );
   }

   return res;
}

void
calc::transformer::add_initial( logic::beliefstate& blfs, logic::term conj )
{
   std::cout << "Adding a conjunct:    " << conj << "\n";

   auto name = fresh_ident( blfs, "initial" );

   std::cout << name << "\n";
   auto decl = logic::belief( logic::bel_decl, name,
                              logic::type( logic::type_truthval ));

   auto pred = blfs. append( std::move( decl ));
 
   push( pred, conj, pol_neg, step_none );
}


void calc::transformer::flush( logic::beliefstate& blfs )
{

   // The processed formula always has to be moved into a local 
   // variable, because the queues may change.

   while( forms. size( ))
   {
      auto f = extract_top( );

      switch( f. last )
      {

      case step_none:
         f. last = step_rmlet; 
         break;  
      case step_rmlet:
         {
            logic::context ctxt = get_context( f. pred, blfs );
            f. form = splitequiv( *this, blfs, ctxt, std::move( f. form ), 0 );
            f. last = step_splitequiv;
            break; 
         }
      case step_splitequiv: 
         {
            f. form = knf( f. form, pol_pos );
            f. last = step_kleening;
            break;
         }
      case step_kleening:
         {
            f. form = alt_disj( f. form ); 
            f. last = step_anf;
            break;
         }
      default:
         print( std::cout );
         std::cout << f << "\n";
         std::cout << "dont know what comes after: " << f. last << "\n";
         throw std::logic_error( "unfinished" );
      }
 
      forms. push_back( std::move(f));
      push_heap( forms. begin( ), forms. end( )); 
   }
 
}

std::pair< logic::term, logic::term > 
calc::transformer::extractsubform( logic::beliefstate& blfs,
                                   const char* namebase,
                                   const logic::context& ctxt,
                                   logic::term ff )
{
   auto pred = fresh_ident( blfs, namebase );
   std::cout << "predicate name will be " << pred << "\n";

   std::cout << "extracting " << ff << "\n";
   
   auto freevars = count_debruijn( ff );
      // In increasing order. That means that the
      // nearest De Bruijn variable comes first.

   auto tp = logic::type( logic::type_func, 
                logic::type( logic::type_truthval ), { } );

   // We need to walk in reverse order, because we want the
   // type of the furthest De Bruijn variable first:

   for( auto it = freevars. end( ); it != freevars. begin( ); )
   {
      -- it;
      size_t vv = it -> first;
      tp. view_func( ). push_back( ctxt. gettype( vv ));
   }

   auto predex = 
      blfs. append( logic::belief( logic::bel_decl, pred, tp ));

   // Now that we have the exact name, we can create the atom: 

   auto atom = logic::term( logic::op_exact, predex );
   atom = logic::term( logic::op_apply, atom, 
                       std::initializer_list< logic::term > ( ));

   auto atom_view = atom. view_apply( );

   // We need to go in reverse order, because we want the
   // type of the furthest De Bruijn variable first:

   for( auto it = freevars. end( ); it != freevars. begin( ); )
   {
      -- it; 
      size_t vv = it -> first; 
      atom_view. push_back( logic::term( logic::op_debruijn, vv ));
   }

   std::cout << "replacing subformula by " << atom << "\n";

   // The normalizing substitution substitutes the variables
   // in f into #0,#1,#2, ...

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

   return std::pair( std::move( atom ), std::move( ff ));
}


void calc::transformer::print( std::ostream& out ) const
{
   out << "Transformer:\n";
   out << "   nr = " << nr << "\n";
   for( const auto& f : forms )
      out << "   " << f << "\n"; 
}

logic::context
calc::get_context( logic::exact pred, const logic::beliefstate& blfs )
{
   const auto& bel = blfs. at( pred ). first; 
   if( bel. sel( ) != logic::bel_decl )
      throw std::logic_error( "predicate not declaration" );

   const auto& tp = bel. view_decl( ). tp( ); 

   if( tp. sel( ) == logic::type_truthval )
      return logic::context( );

   if( tp. sel( ) == logic::type_func )
   {
      auto f = tp. view_func( );

      logic::context res;
      for( size_t i = 0; i != f. size( ); ++ i ) 
         res. append( "V", f.arg(i));
   
      return res;
   }

   throw std::logic_error( "get_context: type is wrong" );
}

