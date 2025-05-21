#include "interpretation.h"

semantics::value 
semantics::lattice::top( logic::selector sel )
{
   switch( sel )
   {
   case logic::op_and:
   case logic::op_kleene_and: 
   case logic::op_forall:
   case logic::op_kleene_forall: 
      return value( prim_truthval, 1 );

   case logic::op_or:
   case logic::op_kleene_or:
   case logic::op_exists:
   case logic::op_kleene_exists:
      return value( prim_truthval, 0 );

   default:
      std::cout << sel << "\n";
      throw std::logic_error( "dont know top" );
   }
}

semantics::value
semantics::lattice::bottom( logic::selector sel )
{
   switch( sel )
   {
   case logic::op_kleene_and:
   case logic::op_kleene_forall:
      return value( prim_truthval, 0 );

   case logic::op_kleene_or:
   case logic::op_kleene_exists:
      return value( prim_truthval, 1 );
   
   case logic::op_and:  
   case logic::op_forall:
   case logic::op_or:
   case logic::op_exists:
      return value( prim_truthval, 2 );

   default:
      std::cout << sel << "\n";
      throw std::logic_error( "dont know bottom" );
   }
}

semantics::value
semantics::lattice::merge( logic::selector sel, value val1, value val2 )
{
   std::cout << "merge " << sel << " : " << val1 << " " << val2 << "\n";
   if( val1. tp != prim_truthval || val2. tp != prim_truthval )
      throw std::logic_error( "only truth values can be merged" );

   switch( sel )
   {
   case logic::op_and: 
   case logic::op_forall:
      if( val1. index == 2 || val2. index == 2 )
         return value( prim_truthval, 2 ); 
      if( val1. index == 0 || val2. index == 0 )
         return value( prim_truthval, 0 );
      return value( prim_truthval, 1 ); 

   case logic::op_kleene_and:
   case logic::op_kleene_forall:
      if( val1. index == 0 || val2. index == 0 )
         return value( prim_truthval, 0 );
      if( val1. index == 2 || val2. index == 2 )
         return value( prim_truthval, 2 );
      return value( prim_truthval, 1 );

   case logic::op_or:
   case logic::op_exists:
      if( val1. index == 2 || val2. index == 2 )
         return value( prim_truthval, 2 );
      if( val1. index == 1 || val2. index == 1 )
         return value( prim_truthval, 1 );
      return value( prim_truthval, 0 );

   case logic::op_kleene_or:
   case logic::op_kleene_exists:
      if( val1. index == 1 || val2. index == 1 )
         return value( prim_truthval, 1 );
      if( val1. index == 2 || val2. index == 2 )
         return value( prim_truthval, 2 );
      return value( prim_truthval, 0 );

   default:
      std::cout << sel << "\n"; 
      throw std::logic_error( "dont know how to merge" );
   }

}


void semantics::interpretation::print( std::ostream& out ) const
{
   out << "Interpretation( " << nrobjects << " ):\n";
   for( const auto& p : mp )
   {
      out << p. first << ":   ";
      out << p. second << "\n";
   }

   if( valuation. size( ))
   {
      out << "valuation:\n";
      for( ssize_t ind = 1 - valuation. size( ); const auto& v : valuation )
      {
         out << "   #" << ind << " : ";
         out << v << "\n";

         ++ ind;
      }
   }
}

semantics::value 
semantics::eval( interpretation& interpr, const logic::term& t )
{
   std::cout << "Eval:\n";
   std::cout << interpr << "\n";
   std::cout << t << "\n";

   using namespace logic;
   switch( t. sel( ))
   {
   case op_debruijn:
      {
         auto db = t. view_debruijn( ); 
         const auto& f = interpr. local( db. index( )); 
         return f( {} );
      }
#if 0
        case op_true:
           return tt;
        case op_false:
            return ff;
        case op_error:
            return ee;
        case op_not:
            return TABLE_NOT[ eval( interpr, t. view_unary( ). sub( ) ) ];
        case op_prop: 
           return TABLE_PROP[ eval(interpr, t.view_unary().sub()) ];
#endif 
   case op_and:
   case op_or: 
      {
         auto current = eval( interpr, t. view_binary( ). sub1( ));
         if( current != lattice::bottom( t. sel( )) )
         {
            current = lattice::merge( t. sel( ), current, 
                           eval( interpr, t. view_binary( ). sub2( )) );
         }
         return current; 
      }
#if 0
        case op_lazy_and:
            return TABLE_AND[ eval(interpr, t. view_binary().sub1()) ][ eval( interpr, t.view_binary().sub2() ) ];
        case op_or:
        case op_lazy_or: // TODO : op_lazy_or is the same as op_or?
            return TABLE_OR[ eval(interpr, t. view_binary().sub1()) ][ eval( interpr, t.view_binary().sub2() ) ];
        case op_equiv:
            return TABLE_EQUIV[ eval(interpr, t. view_binary().sub1()) ][ eval( interpr, t.view_binary().sub2() ) ];
        case op_implies:
            return TABLE_IMPLIES[ eval(interpr, t. view_binary().sub1()) ][ eval( interpr, t.view_binary().sub2() ) ];
#endif
   case op_kleene_and:
   case op_kleene_or:
      {
         auto current = lattice::top( t. sel( ));
         const auto bottom = lattice::bottom( t. sel( ));
         auto kl = t. view_kleene( );
         for( size_t i = 0; i != kl. size( ); ++ i )
         {
            current = lattice::merge( t. sel( ), current,  
                                      eval( interpr, kl. sub(i)) ); 
            if( current == bottom )
               return bottom; 
         }
         return current;
      }

   case op_forall:
   case op_kleene_forall:
   case op_exists:
   case op_kleene_exists: 
      {
         const auto bottom = lattice::bottom( t. sel( ));
         auto current = lattice::top( t. sel( ));
         update_quant( current, bottom, interpr, t, 0 ); 
         return current; 
      }
   case op_apply:
      {
         auto a = t. view_apply( );
         const auto& f = eval_func( interpr, a. func( )); 
         std::vector< value > args;
         for( size_t i = 0; i != a. size( ); ++ i )
            args. push_back( eval( interpr, a. arg(i)) );
         return f( args );  
      }
   }
   std::cout << t. sel( ) << "\n";
   throw std::logic_error( "dont know how to evaluate" );
}

void
semantics::update_quant( value& current, const value& worst,
                         interpretation& interpr, 
                         const logic::term& quant, size_t ind )
{
   std::cout << "eval quant: " << quant << "\n";
   std::cout << "ind = " << ind << "\n";
   auto q = quant. view_quant( );

   if( ind < q. size( ))
   {
      function& f = 
         interpr. push( zero_function( q. var( ind). tp, interpr. nrobjects ));

      if( f. can_exist( ))
      {
         bool first = true;
         while( first || !f. allzeroes( ))
         {
            update_quant( current, worst, interpr, quant, ind + 1 );
            if( current == worst )
            {
               interpr. pop( );
               return; 
            } 
       
            ++ f;
            first = false;
         }
      }
      interpr. pop( ); 
      return; 
   }
   else
   {
      auto val = eval( interpr, q. body( )); 
      current = lattice::merge( quant. sel( ), current, val );  
   }
}

const semantics::function&
semantics::eval_func( interpretation& interpr, const logic::term& t )
{
   std::cout << "Eval func " << t << "\n";
   switch( t. sel( ))
   {
   case logic::op_unchecked:
      return interpr. at( t. view_unchecked( ). id( ));    
   case logic::op_debruijn:
      return interpr. local( t. view_debruijn( ). index( )); 
   }
   throw std::logic_error( "dont know how to evaluate function" ); 
}

namespace
{
   std::pair< semantics::primtype, unsigned int > 
   convtype( logic::selector sel, unsigned int nrobjects )
   {
      if( sel == logic::type_obj )
         return { semantics::prim_obj, nrobjects };

      if( sel == logic::type_form )
         return { semantics::prim_truthval, 3 };

      throw std::logic_error( "cannot convert type" );
   }
}

semantics::function 
semantics::zero_function( logic::type tp, unsigned int nrobjects )
{
   std::vector< std::pair< primtype, unsigned >> argtypes;
 
   while( tp. sel( ) == logic::type_func )
   {
      auto f = tp. view_func( );
      for( size_t i = 0; i != f. size( ); ++ i )
         argtypes. push_back( convtype( f. arg(i). sel( ), nrobjects ));
      tp = f. result( ); 
   }

   return function( std::move( argtypes ), convtype( tp. sel( ), nrobjects )); 
}

void 
semantics::check_preceq( std::vector< identtype > :: const_iterator id1,
                         std::vector< identtype > :: const_iterator id2, 
                         const logic::term& from, const logic::term& into,
                         interpretation& interpr )
{
   std::cout << "entering check_preceq:\n";
 
   if( id1 != id2 )
   {
      std::cout << *id1 << "\n";
      function& f = interpr. extend( id1 -> id, 
                             zero_function( id1 -> tp, interpr. nrobjects ));

      if( f. can_exist( ))
      {
         ++ id1;
         bool first = true;
         while( first || !f. allzeroes( ))
         {
            std::cout << f << "\n";

            ++ f;
            first = false;
            check_preceq( id1, id2, from, into, interpr );  
         }
         -- id1;
         interpr. retract( id1 -> id );  
      }
      else
         throw std::runtime_error( "range is empty" );
   }
   else
   {
      std::cout << interpr << "\n";
      value from_val = eval( interpr, from );
      value into_val = eval( interpr, into );

      std::cout << "from val " << from_val << "\n";
      std::cout << "into val " << into_val << "\n";

      // if( from_val != into_val )
      //   throw std::runtime_error( "equivalence failed" );

      if( !preceq( from_val, into_val ))
         throw std::runtime_error( "preceq failed" );
   }
}

void 
semantics::check_preceq( const std::vector< identtype > & idents,
                         const logic::term& from, const logic::term& into ) 
{
   const unsigned int maxdomain = 4;
   std::cout << "should be made 0 later\n";
   for( unsigned int d = 1; d < maxdomain; ++ d )
   {
      auto interpr = interpretation(d); 
      check_preceq( idents. begin( ), idents. end( ), from, into, interpr ); 
   }
}

