
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
      return { 140, 1 };
   case op_lazy_or:
      return { 130, 1 };
   case op_lazy_implies:
      return { 121, 1 };

   case op_forall:
   case op_exists:
   case op_kleene_forall:
   case op_kleene_exists:
   case op_lambda:
   case op_let: 
      return { 0, 1 };
 
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
      needed = true;
      return;
   }

   if( env. second && attr. right && env. second >= attr. right )
   {
      needed = true;
      return;
   }
}

void 
logic::pretty::parentheses::opening( std::ostream& out ) const
{
   if( needed )
      out << "( ";
}

void 
logic::pretty::parentheses::closing( std::ostream& out ) const
{
   if( needed ) 
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
   case type_form:
      out << tp; 
      return;

   case type_struct:
      {
         exact ex = tp. view_struct( ). def( );
         if( blfs. contains( ex ))
         { 
            const auto& id = blfs. at( ex ). name( );
            out << id;
         }
         else
            out << ex;
      }
      return;

   case type_unchecked:
      out << '\'' << tp. view_unchecked( ). id( ) << '\'';
      return;
   }

   if( tp. sel( ) != type_func )
      throw std::runtime_error( "structural type must be functional" );

   if constexpr( true )
   {
      auto f = tp. view_func( );    
      print( out, blfs, f. result( ), between( env, {500,0} ));
      out << '(';
      for( size_t i = 0; i != f. size( ); ++ i )
      {
         if(i) out << ',';
         print( out, blfs, f. arg(i), {0,0} );
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

      par. opening( out );
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
      out << " --> ";
      print( out, blfs, f. result( ), between( arrow_attr, env ));
      par. closing( out );
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
         out << ", ";
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
            const auto& id = blfs. at( ex ). name( );
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
         par.opening( out ); 

         if( t. sel( ) == op_not )
            out << "! ";
         if( t. sel( ) == op_prop )
            out << "# ";

         print( out, blfs, names, un. sub( ), between( ourattr, env ));
         par.closing( out );
      }
      return;
   
   case op_false:
      out << "FF"; return;
   case op_error:
      out << "EE"; return;
   case op_true:
      out << "TT"; return;
   
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

      par.opening( out );
      print( out, blfs, names, bin. sub1( ), between( env, ourattr ));

      switch( t. sel( ))
      {
      case op_and:      out << " & "; break;
      case op_or:       out << " | "; break;
      case op_implies:  out << " -> "; break;
      case op_equiv:    out << " <-> "; break;
      case op_equals:   out << " == "; break;

      default: out << " ??? "; break;
      }
         
      print( out, blfs, names, bin. sub2( ), between( ourattr, env ));

      par.closing( out );
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

      par.opening( out );
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
      par.closing( out );

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
         par. opening( out );

         print( out, blfs, names, kl. sub(0), between( env, ourattr ));
     
         for( size_t i = 1; i != kl. size( ); ++ i )
         {
            if( t. sel( ) == op_kleene_and )
               out << " && ";
            else
               out << " || ";
 
            print( out, blfs, names, kl. sub(i), 
                   i + 1 != kl. size( ) ?
                      between( ourattr, ourattr ) :
                      between( ourattr, env ));
         }

         par. closing( out );
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
         
         par. opening( out );

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

         par. closing( out );
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

         par. opening( out );
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
  
         par. closing( out );
         return;
      }

   case op_lambda:
      {
         const size_t ss = names. size( );
         auto ourattr = getattractions( t. sel( ));
         
         parentheses par;
         par. check( ourattr, env ); 
         if( par ) env = {0,0};    

         par.opening( out );

         out << "?? ("; 

         auto lamb = t. view_lambda( );
         print( out, blfs, names,
                [&lamb]( size_t i ) { return lamb. var(i); }, lamb. size( ));
         out << " ) ";

         print(out, blfs, names, lamb.body(), between( ourattr, env ));
         par. closing( out );
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

         par. opening( out );

         out << "LET";

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

         out << " IN ";
         print( out, blfs, names, *p, between( ourattr, env )); 
         par. closing( out );
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


void 
logic::pretty::print( std::ostream& out,
                      const beliefstate& blfs,  
                      const logic::belief& bel )
{
   switch( bel. sel( ))
   {
   case logic::bel_symbol:
      {
         out << " : ";
         auto sym = bel. view_symbol( );
         pretty::print( out, blfs, sym. tp( ), {0,0} );
         out << "\n";
         return;
      }

   case logic::bel_def:
      {
         out << " := ";
         auto def = bel. view_def( );
         context ctxt; 
         pretty::print( out, blfs, ctxt, def. val( )); 
         out << " : ";
         pretty::print( out, blfs, def. tp( ), {0,0} );
         out << "\n";
         return;
      }
#if 0      
   case logic::bel_asm:
      {
         auto assume = bel. view_asm( );
         pretty::print( out, names, assume. form( )); 
         out << "\n";
         return;
      }
#endif

   case logic::bel_thm:
      {
         out << "  : theorem ";
         auto thm = bel. view_thm( );
         context ctxt;
         pretty::print( out, blfs, ctxt, thm. form( ));
         // pretty::print( out, names, thm. proof( ) );
         out << "\n";
         return; 
      }

     case logic::bel_axiom:
      {
         out << "   : ";
         auto ax = bel. view_axiom( );
         context ctxt;
         pretty::print( out, blfs, ctxt, ax. form( ));
         out << "\n";
         return;
      }

   case logic::bel_supp:
      {
         out << "   : "; 
         auto sp = bel. view_supp( );
         context ctxt;
         pretty::print( out, blfs, ctxt, sp. form( ));
         out << "\n";
         return; 
      }

   case logic::bel_struct:
      {
         out << "   : struct\n"; 
         const auto& def = bel. view_struct( ). def( ); 
         for( const auto& fld : def )
         {
            out << "      " << fld. name << " : ";
            pretty::print( out, blfs, fld. tp, {0,0} );
            out << "\n";
         } 
         return;
      }

   case logic::bel_constr:
      {
         out << "   : constructor of " << bel. view_constr( ). tp( ) << "\n";
         return; 
      }

   case logic::bel_fld:
      {
         auto fld = bel. view_field( );
         out << "   : field #" << fld. offset( ) << " of ";
         out << fld. sdef( ) << "\n";
         return;
      }
   }
   out << "print belief: " << bel. sel( ) << "\n";
   throw std::runtime_error( "unknown selector" );
}


