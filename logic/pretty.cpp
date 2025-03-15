
#include "pretty.h"
#include "kbo.h"


logic::pretty::attractions 
logic::pretty::getattractions( logic::selector sel )
{
   switch( sel )
   {
   case op_not:
   case op_prop:
      return { 0, 150 };

   case op_and:
   case op_kleene_and: 
      return { 140, 141 };

   case op_or:
   case op_kleene_or:
      return { 130, 131 };

   case op_implies:
      return { 121, 120 };
   case op_equiv:
      return { 110, 110 };
   case op_equals:
      return { 160, 160 }; 

   case op_lazy_and:
      return { 140, 141 };
   case op_lazy_or:
      return { 130, 131 };
   case op_lazy_implies:
      return { 121, 120 };

   case op_forall:
   case op_exists:
   case op_kleene_forall:
   case op_kleene_exists:
   case op_lambda:
   case op_let: 
      return { 0, 100 };
 
   case op_apply:
      return { 190, 191 };

   }
   std::cout << sel << "\n";
   throw std::runtime_error( "dont know attraction" );
}


void
logic::pretty::parentheses::check( attractions attr,
                              std::pair< unsigned int, unsigned int > env )
{
   if( env. first && attr. left && env. first >= attr. left )
   {
      ++ nr;
      return;
   }

   if( env. second && attr. right && env. second >= attr. right )
   {
      ++ nr;
      return;
   }
}

void 
logic::pretty::parentheses::open( std::ostream& out ) const
{
   for( unsigned int i = 0; i != nr; ++ i )
      out << "( ";
}

void 
logic::pretty::parentheses::close( std::ostream& out ) const
{
   for( unsigned int i = 0; i != nr; ++ i )
      out << " )";
}

// One could try to use => :

void logic::pretty::print( std::ostream& out, const beliefstate& blfs,
                const type& tp, std::pair< unsigned int, unsigned int > env ) 
{
  
   // The following types are always printed the same:

   switch( tp. sel( ))
   {
   case type_obj:
      out << "O";
      return;
   case type_truthval:
      out << "T";
      return;

   case type_struct:
      {
         exact ex = tp. view_struct( ). def( );
         if( blfs. contains( ex ))
         { 
            const auto& id = blfs. at( ex ). first. name( );
            out << id;
         }
         else
            out << ex;
      }
      return;

   case type_unchecked:
      out << '\''<< tp. view_unchecked( ). id( ) << '\'';
      return;
   }

   if( tp. sel( ) != type_func )
      throw std::runtime_error( "structural type must be functional" );

   if constexpr( csyntax_types )
   {
      auto f = tp. view_func( );    
      out << f. result( ) << '(';
      for( size_t i = 0; i != f. size( ); ++ i )
      {
         if(i) out << ',';
         out << f. arg(i);
      }
      out << ')';
   }
   else 
   {
      const attractions arrow_attr = { 121, 120 };
      const attractions prod_attr = { 500, 501 }; 

      parentheses par;
      par. check( arrow_attr, env ); 
      if( par ) env = {0,0}; 

      par. open( out );
      auto f = tp. view_func( );
            
      if( f. size( ) == 0 )
         out << "1";

      if( f. size( ) == 1 ) 
         print( out, blfs, f. arg(0), between( env, arrow_attr ));

      if( f. size( ) >= 2 )
      { 
         print( out, blfs, f. arg(0), between( env, prod_attr ));
         out << " * ";
         for( size_t i = 1; i+1 < f. size( ); ++ i )
         {
             print( out, blfs, f. arg(i), between( prod_attr, prod_attr ));
             out << " * ";
         }
         print( out, blfs, f. arg( f. size( ) - 1 ),  
                               between( prod_attr, arrow_attr ));
      }
      out << " -> ";
      print( out, blfs, f. result( ), between( arrow_attr, env ));
      par. close( out );
   }
}


void 
logic::pretty::print( std::ostream& out, const beliefstate& blfs,
           uniquenamestack& names, 
           const std::function< vartype( size_t ) > & vt, size_t sz )
{
   // If two consecutive variables have the same type, 
   // we print them together:

   size_t v = 0; 
   while( v != sz ) 
   {
      // [ v, e ) are variables with the same type.

      size_t e = v + 1;
      while( e != sz && equal( vt(v).tp, vt(e).tp ))
         ++ e;

      if(v)
         out << "; ";
      else
         out << " ";

      for( size_t k = v; k != e; ++ k ) 
      {
         if( k != v ) 
            out << ",";

         out << names. extend( vt(k). pref ); 
      }

      out << ": ";
      print( out, blfs, vt(v).tp, {0,0} );

      v = e; 
   }
}


// The attractions in env come from different operators.
// env. first is the left attraction of the operator to the right of us.
// env. second is sthe right attraction of the operator to the left of us.

void 
logic::pretty::print( std::ostream& out, const beliefstate& blfs,
          uniquenamestack& names, const term& t, 
          std::pair< unsigned int, unsigned int > env )       
{
#if 0
   out << names << "\n";
   out << "pretty: " << t << " " << env << "\n";
#endif

   switch( t. sel( ) ) 
   {
   case op_debruijn:
      {
         size_t ind = t. view_debruijn( ). index( );

         if( ind < names. size( ))
            out << names. getname( ind );
         else
            out << '#' << ind;
         return;
      } 

   case op_unchecked: 
      out << '\'' << t. view_unchecked( ). id() << '\'';
         // We need to do something to show it. 
      break;
  
   case op_exact: 
      {
         exact ex = t. view_exact( ). ex( );
         if( blfs. contains( ex ))
         { 
            const auto& id = blfs. at( ex ).first. name( );
            if( id. size( ) == 1 && !names. issafe( id. at(0)) )
               out << "::";
            out << id;
         }
         else
            out << ex;
      }
      return;

   case op_not:
   case op_prop:
      {
         auto un = t. view_unary( );
         auto ourattr = getattractions( t. sel( )); 

         parentheses par;
         par. check( ourattr, env );
         if( par ) env = {0,0};
         par.open( out ); 

         if( t. sel( ) == op_not )
            out << "! ";
         if( t. sel( ) == op_prop )
            out << "# ";

         print( out, blfs, names, un. sub( ), between( ourattr, env ));
         par.close( out );
      }
      return;
   
   case op_false:
      out << "FALSE"; return;
   case op_error:
      out << "ERROR"; return;
   case op_true:
      out << "TRUE"; return;
   
   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
   case op_equals:
   {
      auto bin = t. view_binary( );
      auto ourattr = getattractions( t. sel( ));
         
      parentheses par;
      par. check( ourattr, env ); 
      if( par ) env = {0,0}; 

      par.open( out );
      print( out, blfs, names, bin. sub1( ), between( env, ourattr ));

      switch( t. sel( ))
      {
      case op_and:      out << " & "; break;
      case op_or:       out << " | "; break;
      case op_implies:  out << " -> "; break;
      case op_equiv:    out << " <-> "; break;
      case op_equals:   out << " = "; break;

      default: out << " ??? "; break;
      }
         
      print( out, blfs, names, bin. sub2( ), between( ourattr, env ));

      par.close( out );
      return;
   }

   case op_lazy_implies:
   case op_lazy_and:
   case op_lazy_or:
   {
      auto bin = t. view_binary( );
      auto ourattr = getattractions( t. sel( ));
         
      parentheses par;

      par.check( ourattr, env ); 
      if( par ) env = {0,0}; 

      par.open( out );
      out << "{ ";
      print( out, blfs, names, bin. sub1( ), {0,0} );
      out << " }";

      switch( t. sel( ))
      {
      case op_lazy_and:          out << " & ";  break;
      case op_lazy_or:           out << " | ";  break;
      case op_lazy_implies:      out << " -> "; break;

      default:                   out << " ??? "; break;
      }
      
      print( out, blfs, names, bin. sub2( ), between( ourattr, env ));
      par.close( out );

      return;
   }

   case op_kleene_and:
   case op_kleene_or:
      {
         auto kl = t. view_kleene( );

         if( kl. size( ) == 0 && t. sel( ) == op_kleene_and ) 
         {
            out << "TRUE"; 
            return;
         }

         if( kl. size( ) == 0 && t. sel( ) == op_kleene_or )
         {
            out << "FALSE";
            return;
         }

         // If we have one argument, we are invisible:
 
         if( kl. size( ) == 1 )
         {
            print( out, blfs, names, kl. sub(0), env );
            return;
         }

         auto ourattr = getattractions( t. sel( ));
         parentheses par;
         par. check( ourattr, env );
         if( par ) env = {0,0};
         par. open( out );

         print( out, blfs, names, kl. sub(0), between( env, ourattr ));
     
         for( size_t i = 1; i != kl. size( ); ++ i )
         {
            if( t. sel( ) == op_and )
               out << " && ";
            else
               out << " || ";
 
            print( out, blfs, names, kl. sub(i), 
                   i + 1 != kl. size( ) ?
                      between( ourattr, ourattr ) :
                      between( ourattr, env ));
         }

         par. close( out );
         return; 
      }

   case op_forall:
   case op_exists:
   case op_kleene_forall:
   case op_kleene_exists:
      {
         auto q = t. view_quant( );
         const size_t ss = names. size( );

         auto ourattr = getattractions( t. sel( ));

         parentheses par;
         par. check( ourattr, env );
         if( par ) env = {0,0};
         
         par. open( out );

         if( t. sel( ) == op_forall || t. sel( ) == op_kleene_forall )
            out << "[";
         if( t. sel( ) == op_exists || t. sel( ) == op_kleene_exists )
            out << "<";

         print( out, blfs, names, 
                [&q]( size_t i ) { return q. var(i); }, q. size( ));

         if( t. sel( ) == op_forall || t. sel( ) == op_kleene_forall )
            out << " ] ";
         if( t. sel( ) == op_exists || t. sel( ) == op_kleene_exists )
            out << " > ";

         print( out, blfs, names, q. body( ), between( ourattr, env ));

         par. close( out );
         names. restore( ss );
         return;
      }

   case op_apply:
      {
         auto appl = t. view_apply( );
         auto ourattr = getattractions( t. sel( ));

         parentheses par;
         par. check( ourattr, env );
         if( par ) 
            env = {0,0};

         par. open( out );
         print( out, blfs, names, appl. func( ), between( env, ourattr ));

         out << '(';
         for( size_t i = 0; i != appl. size( ); ++ i )
         {
            if( i != 0 )
               out << ", ";
            else
               out << ' ';
            print( out, blfs, names, appl. arg(i), {0,0} );
         }
         out << " )";
  
         par. close( out );
         return;
      }

   case op_lambda:
      {
         const size_t ss = names. size( );
         auto ourattr = getattractions( t. sel( ));
         
         parentheses par;
         par. check( ourattr, env ); 
         if( par ) env = {0,0};    

         par.open( out );

         out << "lambda"; 

         auto lamb = t. view_lambda( );
         print( out, blfs, names,
                [&lamb]( size_t i ) { return lamb. var(i); }, lamb. size( ));
         out << " in ";

         print(out, blfs, names, lamb.body(), between( ourattr, env ));
         par.close( out );
         names. restore( ss );
         return;
      }
       
   case logic::op_let:
      {
         const size_t ss = names. size( );
         auto ourattr = getattractions( t. sel( ));

         parentheses par;
         par. check( ourattr, env );
         if( par ) env = {0,0};

         par. open( out );

         out << "let";

         size_t nr = 0;

         // Could this use of pointers be eliminated?

         const auto* p = &t; 
         while( p -> sel( ) == op_let )
         {
            auto let = p -> view_let( );  

            if( nr ) 
               out << ", ";
            else
               out << " ";

            out << names. extend( let. var(). pref ); 
            names. restore( names. size( ) - 1 );
            out << ": "; 
            print( out, blfs, let. var(). tp, {0,0} ); 
            out << " := ";
            names. extend( let. var(). pref );
            print( out, blfs, names, let. val( ), {0,0} );
  
            p = &let. body( );
            ++ nr;
         }

         out << " in ";
         print( out, blfs, names, *p, between( ourattr, env )); 
         par. close( out );
         names. restore( ss );
         return;
      }

   default:
      out << "UGLY( " << t << ")" << "Sel:" << t.sel();
      return; 
   }
}


void
logic::pretty::print( std::ostream& out, const beliefstate& blfs,
            context& ctxt, const term& t )
{
   uniquenamestack names = getnames( ctxt, ctxt. size( ));
   print( out, blfs, names, t, {0,0} );
}


#if 0

void pretty::print( std::ostream& out,
                    uniquenamestack& names,
                    const logic::belief& bel )
{
   switch( bel. sel( ) )
   {
   case logic::bel_decl:
      {
         auto decl = bel. view_decl( );
         pretty::print( out, decl. tp( ) );
         out << "\n";
         return;
      }

   case logic::bel_def:
      {
         auto def = bel. view_def( );
         pretty::print( out, def. tp( ) );
         out << " := ";
         pretty::print( out, names, def. val( ) ); 
         out << "\n";
         return;
      }
      
   case logic::bel_asm:
      {
         auto assume = bel. view_asm( );
         pretty::print( out, names, assume. form( ) ); 
         out << "\n";
         return;
      }

   case logic::bel_thm:
      {
         auto thm = bel. view_thm( );
         pretty::print( out, names, thm. form( ) );
         out << ",   proof = ";
         pretty::print( out, names, thm. proof( ) );
         out << "\n";
         return; 
      }

   case logic::bel_thm_file:
      {
         auto thm = bel. view_thm_file( );
         pretty::print( out, names, thm. form( ) );
         out << "   (proof is in " << thm. prooffile( ) << ")\n";
         return; 
      }

   }
   out << "print belief: " << bel. sel( ) << "\n";
   throw std::runtime_error( "unknown selector" );
}
#endif

logic::pretty::uniquenamestack
logic::pretty::print( std::ostream& out, 
                      const beliefstate& blfs, const logic::context& ctxt )
{
   out << "Context:\n"
;
   size_t db = ctxt. size( );
      // De Bruijn index.
 
   uniquenamestack names; 

   while( db )
   {
      -- db;

      out << "   ";
      out << names. extend( ctxt. getname( db ));   // The name made unique.
      out << " : ";
      print( out, blfs, ctxt. gettype( db ), {0,0} );
      out << '\n';
   }
   if constexpr( false ) 
   {
      out << "this is the ugly version of this context:\n";
      out << ctxt << "\n";
   }

   return names; 
}

logic::pretty::uniquenamestack
logic::pretty::getnames( const logic::context& ctxt, size_t ss )
{
   uniquenamestack names;

   if( ss > ctxt. size( ))
   {
      std::cout << "cutoff size " << ss << "/" << ctxt. size( ) << " too big\n";
      throw std::runtime_error( "too big" );
   }

   // db = 'De Bruijn':

   size_t db = ss;
   while( db ) 
   {
      -- db;
      names. extend( ctxt. getname( db )); 
   }

   return names;
}

#if 0
void output::print( std::ostream& out, const logic::beliefstate& bel )
{
   out << "Belief State:\n";
#if 0
   uniquenamestack names;

   for( size_t i = 0; i != bel. size( ); ++ i )
   {
      out << "   " << i << "   " << bel. at(i). first << "  : ";
      print( out, names, bel. at(i). second );
   }

   if( false )
   {
      out << "this is the ugly version of this belief state:\n";
      out << bel << "\n";
   }
#endif
   out << "\n";
}
#endif

#if 0
void pretty::print( std::ostream& out, uniquenamestack& names, 
                    const logic::error& err )
{
   switch( err. sel( ))
   {
   case logic::err_index:
      {
         auto ind = err. view_index( );
         out << ind. message( ) << "   #" << ind. index( ) << "\n";
         return;
      }

   case logic::err_typediff:
      {
         auto diff = err. view_typediff( );
         out << diff. message( ) << "   ";
         out << "got "; print( out, diff. received( ));
         out << " instead of "; print( out, diff. expected( ));
         out << "\n";
         return;
      }

   case logic::err_wrongtype:
      {
         auto wrong = err. view_wrongtype( );
         out << wrong. message( ) << "   ";
         print( out, wrong. tp( ));
         out << "\n";
         return;
      }

   case logic::err_ident:
      {
         auto id = err. view_ident( );
         out << id. message( ) << "   " << id. ident( ) << "\n";
         return;
      }

   case logic::err_cannotapply:
      {
         auto cant = err. view_cannotapply( );
         out << cant. message( ) << "   ";
         for( size_t i = 0; i != cant. size( ); ++ i )
         {
            if(i) out << ", "; 
            print( std::cout, names, cant. form(i)); 
         }
         out << "\n";
         return; 
      }  
   }

   std::cerr << "error " << err. sel( ) << "\n";
   throw std::runtime_error( "dont know how to pretty-print" ); 
}

#endif

