
#include "pretty.h"

const char* logic::pretty::getcstring( selector sel )
{
   switch( sel ) 
   {
#if 0
      // nullary terms:

      { logic::sel_false, "False" },
      { logic::sel_true, "True" },
      { logic::sel_emptyset, "{}" },
      { logic::sel_infset, "inf" },
#endif

   case op_not:
      return "~ ";
   case op_prop:
      return "#";

#if 0
	      // binary terms:

	      { logic::sel_and, "/\\" },
	      { logic::sel_or, "\\/" },
	      { logic::sel_implies, "->" },
	      { logic::sel_equiv, "<->" },
	      { logic::sel_equals, "=" },
	      { logic::sel_in, "in" },
	      { logic::sel_subset, "subset" },
	      { logic::sel_insert, "" },
	      { logic::sel_sep, "sep" },
	      { logic::sel_repl, "repl" },
	      { logic::prf_inst, "inst" },
	      { logic::prf_abbr, "abbr" },
	      { logic::prf_exists, "exists" },
	#endif

   case op_forall:
   case op_kleene_forall:
      return "[";
   case op_exists:
   case op_kleene_exists:
      return "<";
	  
	#if 0
	      // ternary terms:

	      { logic::prf_disj, "disj" },

	      // appl terms
	      { logic::sel_appl, "" },

	      // lambda terms
	      { logic::sel_lambda, "=>" },

	      // exp terms
	      { logic::prf_exp, "exp" },

	      // unfinished terms
	      { logic::prf_unfinished, "unfinished" }
	#endif
	   }
	   std::cout << sel << "\n";
	   throw std::runtime_error( "dont know c-string" );
	}


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


// One could try to use => :

void logic::pretty::print( std::ostream &out, const beliefstate& blfs,
			   const type& tp, attractions envattr ) 
{
   out << tp; 
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
          context& ctxt, uniquenamestack& names, 
          const term& t, attractions envattr )       
{
#if 0
   out << ctxt << "\n";
   out << "pretty: " << t << " " << envattr << "\n";
#endif

   if( ctxt. size( ) != names. size( ))
      throw std::runtime_error( "sizes not equal" );

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
            out << '#' << ind << "/" << names. size( ) << "\n";
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
	 parprinter par( out );
         auto ourattr = getattractions( t. sel( )); 
	 par. printif( envattr. left >= ourattr. right );
         out << pretty::getcstring( t. sel( )); 
          
         print( out, blfs, ctxt, names, un. sub( ), 
                { ourattr. right, envattr. left } );
      }
      return;
      
#if 0
      case logic::sel_union:
      case logic::sel_pow:
      case logic::sel_unique:
      case logic::prf_and1:
      case logic::prf_and2:
      case logic::prf_taut:
      case logic::prf_ext1:
      case logic::prf_ext2:
         {
            auto unary_t = t. view_unary( );
            out << operator_rep. at( t. sel( ) ) << "(";
            print( out, names, unary_t. sub( ), 0, 0 );
            out << ")";
            return;
         }

      case logic::sel_and:
      case logic::sel_or:
      case logic::sel_implies:
      case logic::sel_equiv:
      case logic::sel_equals:
      case logic::sel_in:
      case logic::sel_subset:
         {
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

         parprinter par( out );

         auto ourattr = getattractions( t. sel( ));
         par. printif( ourattr. right <= envattr. left );
       
         const char* repr = pretty::getcstring( t. sel( ));

         out << repr; 
         for( size_t i = 0; i != q. size( ); ++ i )
         {
            if( i == 0 )
               out << " ";
            else
               out << ", ";
            
            ctxt. extend( q. var(i). pref, q. var(i). tp );
            out << names. extend( q. var(i). pref );
            out << " : ";
            print( out, blfs, q. var(i). tp, attractions(0,0) );
         }
   
         if( repr[0] == '[' ) out << " ] ";
         if( repr[0] == '>' ) out << " > ";

         print( out, blfs, ctxt, names, q. body( ),
                { ourattr. right, envattr. right } );
 
         ctxt. restore( ss );
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
            print( out, blfs, ctxt, names, appl. func( ), { 0,0 } );
               // Attraction don't matter for an identifier.

            out << '(';
            for( size_t i = 0; i != appl. size( ); ++ i )
            {
               if( i != 0 )
                  out << ", ";
               else
                  out << ' ';
               print( out, blfs, ctxt, names, appl. arg(i), { 0,0 } );
            }
            out << " )";
            return;
         }
         else
         {
            out << "hard\n";
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
   default:
      std::cout << "pretty print, selector = " << t. sel( ) << "\n";
      throw std::logic_error("no maching selector for in pretty_print(term)");
   }
}


void
logic::pretty::print( std::ostream& out, const beliefstate& blfs,
            context& ctxt, const term& t, attractions attr )
{
   uniquenamestack names;
   addnames( ctxt, names );
   print( out, blfs, ctxt, names, t, attr );
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

#if 0
output::uniquenamestack
output::print( std::ostream& out, const logic::context& ctxt )
{
   out << "Context:\n";
   size_t var = ctxt. size( );
   
   uniquenamestack names; 
   while( var )
   {
      -- var;
      const auto& bel = ctxt. getbelief( var );

      // We need to see the name without extending names,
      // because assumptions and definitions become effective only
      // when they are ended.

      auto n = names. nextname( ctxt. getname( var )); 
      out << "   " << n << " : ";
      pretty::print( out, names, bel );
      names. extend( ctxt. getname( var ));
   }
   if( false ) 
   {
      out << "this is the ugly version of this context:\n";
      out << ctxt << "\n";
   }

   return names; 
}
#endif

void 
logic::pretty::addnames( const logic::context& ctxt, 
                         uniquenamestack& names )
{
   if( names. size( ) > ctxt. size( ))
      throw std::runtime_error( "addnames: names longer than ctxt" );

   // db = 'De Bruijn':

   size_t db = ctxt. size( ) - names. size( );
   while( db ) 
   {
      -- db;
      names. extend( ctxt. getname( db )); 
   }
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

