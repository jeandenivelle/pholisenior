
#include "pretty.h"

logic::pretty::attractions 
logic::pretty::getattractions( logic::selector sel )
{
   switch( sel )
   {
#if 0
	      // id terms
	      { logic::sel_ident, { 0, 0 } },

	      // debruijn terms
	      { logic::sel_debruijn, { 0, 0 } },
	      
	      // nullary terms

#endif

   case op_not:
   case op_prop:
      return { 0, 150 };

   case op_and:
      return { 140, 141 };
   case op_or:
      return { 130, 131 };
   case op_implies:
      return { 121, 120 };
   case op_equiv:
      return { 110, 110 };
   case op_equals:
      return { 160, 160 }; 

   case op_lazy_and:
      return { 141, 140 };
   case op_lazy_or:
      return { 131, 130 };
   case op_lazy_implies:
      return { 121, 120 };

#if 0
      // unary terms

	      { logic::sel_union, { 0, 0 } },
	      { logic::sel_pow, { 0, 0 } },
	      { logic::sel_unique, { 0, 0 } },
	      { logic::prf_and1, { 0, 0 } },
	      { logic::prf_and2, { 0, 0 } },
	      { logic::prf_taut, { 0, 0 } },
	      { logic::prf_ext1, { 0, 0 } },
	      { logic::prf_ext2, { 0, 0 } },

	      // binary terms

	      { logic::sel_and, { 60, 61 } },
	      { logic::sel_or, { 50, 51 } },
	      { logic::sel_implies, { 41, 40 } },
	      { logic::sel_equiv, { 41, 41 } },
	      { logic::sel_equals, { 70, 70 } },
	      { logic::sel_in, { 70, 70 } },
	      { logic::sel_subset, { 70, 70 } },
	      { logic::sel_insert, { 0, 0 } },
	      { logic::sel_sep, { 0, 0 } },
	      { logic::sel_repl, { 0, 0 } },
	      { logic::prf_inst, { 0, 0 } },
	      { logic::prf_abbr, { 0, 0 } },
	      { logic::prf_exists, { 0, 0 } },

	      // ternary terms

	      { logic::prf_disj, { 0, 0 } },

	#endif
   case op_forall:
   case op_exists:
   case op_kleene_forall:
   case op_kleene_exists:
      return { 0, 100 };

   case op_lambda: {
      return {15, 16};
   }

#if 0
	      // appl terms
	      { logic::sel_appl, { 21, 20 } },

	      // lambda terms
	      { logic::sel_lambda, { 15, 16 } },

	      // exp terms
	      { logic::prf_exp, { 0, 0 } },

	      // unfinished terms
	      { logic::prf_unfinished, { 0, 0 } }

#endif
   }
   std::cout << sel << "\n";
   throw std::runtime_error( "dont know attraction" );
}


bool
logic::pretty::parentheses::check( attractions attr,
                              std::pair< unsigned int, unsigned int > env )
{
   // std::cout << "checking " << attr << " in environment " << env << "\n";
   if( env. first || env. second )
   {
      if( attr. left <= env. first )
      {
         ++ nr;
         return true;
      }
      if( attr. right <= env. second )
      {
         ++ nr;
         return true;
      }
      return false;
   }
   else
      return false;     // Environment cannot attract anything.
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

void logic::pretty::print( std::ostream &out, const beliefstate& blfs,
			   const type& tp, std::pair< unsigned int, unsigned int > env ) 
{
   if constexpr( false )
      out << tp; 
   else {
      switch (tp.sel())
      {
      case logic::type_obj:
         out << "O";
         return;
      case logic::type_truthval:
         out << "T";
         return;
      case logic::type_struct:
         out << blfs. at( tp. view_struct( ). def( )). first. name( );
         return;
      case logic::type_unchecked:
         out << tp. view_unchecked( ). id( );
         return;
 
      case logic::type_func: 
         {
            const attractions arrow_attr = { 121, 120 };
            const attractions prod_attr = { 500, 501 }; 

            parentheses par;
            par. check( arrow_attr, env ); 
            if( par ) env = {0,0}; 

            par. open( out );
	         auto f = tp. view_func( );
            
            if( f. size( ) == 0 )
               out << "( )";
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
   }

#if 0
   switch ( t. sel( ) ) 
   {
   case logic::sel_set:
      stream << "S";
      return;
   case logic::sel_truthval:
      stream << "T";
      return;
   case logic::sel_belief:
      stream << "B";
      return;
   case logic::sel_contr:
      stream << "C";
      return;
   case logic::sel_func: 
      {
	 logic::type::const_func func_t = t. view_func( );
	 print( stream, func_t. result( )); 
	 stream << "(";
	 for ( size_t i = 0; i < func_t. size( ); ++i ) 
	 {
	    if(i) stream << ',';
	    print( stream, func_t. arg(i) );
	 }
	 stream << ")";
      }
   }
#endif
}


// The attractions in envattr come from different operators.
// envattr.right is the left attraction of the operator to the right of us.
// envattr.left is sthe right attraction of the operator to the left of us.

void 
logic::pretty::print( std::ostream& out, const beliefstate& blfs,
          uniquenamestack& names, const term& t, std::pair< unsigned int, unsigned int > env )       
{
#if 0
   out << ctxt << "\n";
   out << "pretty: " << t << " " << envattr << "\n";
#endif

   switch( t. sel( ) ) 
   {

#if 0
   case logic::sel_ident:
	 {
	    auto id_t = t. view_id( );
	    out << id_t. ident( );
	    return;
	 } 
#endif
   case op_debruijn:
      {
         size_t ind = t. view_debruijn( ). index( );

         if( ind >= names. size( ))
         {
            std::cout << '#' << ind << "/" << names. size( ) << "\n";
            throw std::runtime_error( "de bruijn index too big" );
         }  
         out << names. getname( ind );
         return;
      } 
#if 0
	      case logic::sel_false:
	      case logic::sel_true:
	      case logic::sel_emptyset:
	      case logic::sel_infset:
		 {
		    out << operator_rep. at( t. sel( ) );
		    return;
		 }

	#endif

   case op_not:
   case op_prop:
      {
	      auto un = t. view_unary( );
         auto ourattr = getattractions( t. sel( )); 

	      //parprinter par( out );
	   #if 0   
         par. printif( envattr. left >= ourattr. right );
         if( t. sel( ) == op_not )
            out << "! ";
         if( t. sel( ) == op_prop )
            out << '#';
      #endif

         print( out, blfs, names, un. sub( ), between(ourattr, env));
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
            
         //parprinter par( out );
         parentheses par;
         par. check( ourattr, env ); 
         if( par ) env = {0,0}; 

         par.open(out);

         print( out, blfs, names, bin. sub1( ), between(env, ourattr) );

         switch( t. sel( ))
         {
         case op_and:      out << " & "; break;
         case op_or:       out << " | "; break;
         case op_implies:  out << " -> "; break;
         case op_equiv:    out << " <-> "; break;
         case op_equals:   out << " = "; break;

         default: out << " ??? "; break;
         }
         
         print( out, blfs, names, bin. sub2( ), between(ourattr, env) );

         par.close(out);

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

      par.open(out);
         
      out << "{";

      print( out, blfs, names, bin. sub1( ),
       between(std::pair<unsigned int, unsigned int>{0,0}, ourattr) );

      out << "}";

      switch( t. sel( ))
      {
      case op_lazy_and:          out << " & ";  break;
      case op_lazy_or:           out << " | ";  break;
      case op_lazy_implies:      out << " -> "; break;

      default:                   out << " ??? "; break;
      }
      
      print( out, blfs, names, bin. sub2( ), between(ourattr, env) );

      par.close(out);

      return;
   }
#if 0
            bool is_in_par = false;
            auto bin = t. view_binary( );

            if( left > l_r_attraction. at( t. sel( )). first || l_r_attraction. at( t. sel( )). second < right )
            {
               is_in_par = true;
               left = 0; 
               right = 0;
            }

            if( is_in_par ) out << "( ";

            print( out, names, bin. sub1( ), left, l_r_attraction. at( t. sel( )). first );
            out << " " << operator_rep. at( t. sel( ) ) << " ";
            print( out, names, bin. sub2( ), l_r_attraction. at( t. sel( )). second, right );

            if( is_in_par ) out << " )";

            return;
      }

      case logic::sel_insert:
         {
            auto insert_t = t. view_binary( );
            out << "{";
            print( out, names, insert_t. sub1( ), 0, 0 );

            const logic::term *sub = &( t. view_binary( ). sub2( ) );
            while( sub-> sel( ) == logic::sel_insert )
            {
               auto sub_insert = sub-> view_binary( );
               out << ", ";
               print( out, names, sub_insert. sub1( ), 0, 0 );
               sub = &( sub_insert. sub2( ) );
            }

            if( sub-> sel( ) != logic::sel_emptyset )
            {
               out << " | "; 
               print( out, names, *sub, 0, 0 );
            }

            out << "}";
            return;
         }

      case logic::sel_sep:
      case logic::sel_repl:
      case logic::prf_inst:
      case logic::prf_exists:
         {
            auto bin = t. view_binary();

            out << operator_rep. at( t. sel( ) ) << "(";
            print( out, names, bin. sub1( ), 0, 0 );
            out << ", ";
            print( out, names, bin. sub2( ), 0, 0 );
            out << ")";
            
            return;
         }

      case logic::prf_disj:
         {
            auto ternary_t = t. view_ternary( );
            
            out << operator_rep. at( t. sel( ) ) << "(";
            print( out, names, ternary_t. sub1( ), 0, 0 );
            out << ", ";
            print( out, names, ternary_t. sub2( ), 0, 0 );
            out << ", ";
            print( out, names, ternary_t. sub3( ), 0, 0 );
            out << ")";

            return;
         }

#endif
   case op_forall:
   case op_exists:
   case op_kleene_forall:
   case op_kleene_exists:
      {
         auto q = t. view_quant( );
         const size_t ss = names. size( );

         auto ourattr = getattractions( t. sel( ));
         // par. printif( ourattr. right <= envattr. left );

         parentheses par;
         par.check(ourattr, env);
         if (par) env = {0,0};
         
         par.open(out);

         if( t. sel( ) == op_forall )
            out << "[";
         if( t. sel( ) == op_exists )
            out << "<";

         for( size_t i = 0; i != q. size( ); ++ i )
         {
            if( i == 0 )
               out << " ";
            else
               out << ", ";
            
            out << names. extend( q. var(i). pref );
            out << ": ";
            print( out, blfs, q. var(i). tp, {0,0} );
         }

         if( t. sel( ) == op_forall )
            out << " ]";
         if( t. sel( ) == op_exists )
            out << " >";


         out << " "; //" : ";
         print( out, blfs, names, q. body( ), between(ourattr, env) );

         par.close(out);

         names. restore( ss );

         return;
      }

   case op_apply:
      {
         auto appl = t. view_apply( );

         if( appl. func( ). sel( ) == op_debruijn ||
             appl. func( ). sel( ) == op_exact ||
             appl. func( ). sel( ) == op_unchecked )
         {
            print( out, blfs, names, appl. func( ), { 0,0 } );
               // Attraction don't matter for an identifier.

            out << '(';
            for( size_t i = 0; i != appl. size( ); ++ i )
            {
               if( i != 0 )
                  out << ", ";
               else
                  out << ' ';
               print( out, blfs, names, appl. arg(i), { 0,0 } );
            }
            out << " )";
            return;
         }
         else
         { 
            while (appl.func().sel() != op_debruijn &&
                   appl.func().sel() != op_exact &&
                   appl.func().sel() != op_unchecked) {
                  appl = appl.func().view_apply();
            }
            print(out, blfs, names, appl.func(), env);
#if 0
            bool is_in_par = false;
            auto appl_t = t. view_appl( );
            auto op_left = l_r_attraction. at( t. sel( ) ). first;
            auto op_right = l_r_attraction. at( t. sel( ) ). second;

            if( appl_t. func( ). sel( ) == logic::sel_ident || appl_t. func( ). sel( ) == logic::sel_debruijn )
            {
               op_left = 1000;
               op_right = 1000;
            }

            if( left > op_left || op_right < right )
            {
               is_in_par = true;
               left = 0;
               right = 0;
            }

            if( is_in_par ) out << "(";

            print( out, names, appl_t. func( ), 0, op_left );
            if( appl_t. func( ). sel( ) != logic::sel_ident && appl_t. func( ). sel( ) != logic::sel_debruijn ) out << '.';
            
            out << "(";
            for( size_t i = 0; i < appl_t. size( ); ++i )
            {
               if( i ) out << ", ";
               print( out, names, appl_t. arg( i ), 0, 0 );
            }
            out << ")";

            if( is_in_par ) out << ")";

#endif
         }
         return;
      }

   case op_lambda:
      {
         auto lamb = t. view_lambda( );
         const size_t ss = names. size( );
         auto ourattr = getattractions( t. sel( ));
         
         // parprinter par( out );
         parentheses par;
         par. check( ourattr, env ); 
         if( par ) env = {0,0};    

         par.open(out);

         out << "\\(";
         for (size_t i = 0; i < lamb.size(); i++ ) {
            if( i == 0 )
               out << " ";
            else
               out << ", ";
            
            out << names. extend( lamb.var(i). pref );
            out << ": ";
            print( out, blfs, lamb.var(i).tp, {0,0} );
         }
         out << ") ";
         print(out, blfs, names, lamb.body(), between(ourattr, env));

         par.close(out);

#if 0
         if( left > l_r_attraction. at( t. sel( ) ). first || l_r_attraction. at( t. sel( ) ). second < right )
            {
               is_in_par = true;
               left = 0;
               right = 0;
            }

            if( is_in_par ) out << "(";

            out << "(";
            for( size_t i = 0; i < lambda_t. size( ); i++ )
            {
               auto uname = names. extend( lambda_t. var(i). pref );

               if(i) out << ", ";
               out << uname << ":";
               pretty::print( out, lambda_t. var( i ).tp );
            }
            out << ") => ";
            print( out, names, lambda_t. body( ), l_r_attraction. at( t. sel( ) ). second, right );
            
            if( is_in_par ) out << ")";
#endif
         names. restore( ss );
         return;
      }
       
#if 0
      case logic::prf_exp:
         {
            auto exp_t = t. view_exp( );

            out << operator_rep. at( t. sel( ) ) << "(";
            print( out, names, exp_t. body( ), 0, 0 );
            out << ", " << exp_t. id( ) << ", " << exp_t. pos( ) << ")";

            return;
         }

      case logic::prf_abbr:
         {
            auto abbr = t. view_abbr( );

            out << "abbreviate( ";
            for( size_t i = 0; i != abbr. size( ); ++i )
            {
               if(i) out << ", ";
               print( out, names, abbr. proof(i), 0, 0 );
            }
            if( abbr. size( )) out << " ) in ";
            print( out, names, abbr. body( ), 0, 0 );
            return; 
         }

      case logic::prf_axiom:
         {
            auto ax = t. view_axiom( ); 
            out << "axiom(";
            for( size_t i = 0; i != ax. size( ); ++i )
            {
               if(i) 
                  out << ", ";
               else
                  out << " ";

               print( out, names, ax. proof(i), 0, 0 );
            }
            out << " )";
            return; 
         }

      case logic::prf_unfinished:
         {
            out << "unfinished( )";
            return; 
         }
#endif
   case op_unchecked: {
      out << t.view_unchecked().id();
      break;
   }
   case op_exact: {
      out << blfs.at(t.view_exact().ex()).first.name();
      break;
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

