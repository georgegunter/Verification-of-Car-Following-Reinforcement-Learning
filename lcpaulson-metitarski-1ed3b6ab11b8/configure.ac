AC_INIT([Metit],[2.2],[lp15 AT cam DOT ac DOT uk],[metit])
AM_INIT_AUTOMAKE
# the following is commented out because Centos 6.4 is only on version 2.63
# AC_PREREQ(2.65)

# check if LDFLAGS exists, if not then set it to
# LDFLAGS='-L/usr/local/lib'
if test -z "$LDFLAGS"
then LDFLAGS='-L/usr/local/lib'
fi

AC_PROG_CXX
AC_PROG_CC
AC_PROG_MAKE_SET
AC_PROG_CPP

AC_ARG_VAR([POLY], [Path to poly executable])
AC_ARG_VAR([METIT], [Path to existing metit binary])

AC_PATH_PROG([POLY], [poly], [], [$POLYPATH:$PATH])
AC_PATH_PROG([METIT], [metit])


 
if test -z "$POLY"
then AC_MSG_ERROR([Missing poly - PolyML available at http://www.polyml.org]);
else
read v_rev v_minor v_major <<EOF
`poly -v|rev |tr "." " "|tr "-" "\n"`
EOF
if test $v_major -lt 5
then AC_MSG_ERROR([PolyML version 5.4.2 or later required]);
fi
if test $v_major -eq 5
then if test $v_minor -lt 4
then AC_MSG_ERROR([PolyML version 5.4.2 or later required]);
fi
fi
if test $v_major -eq 5
then if test $v_minor -eq 4
then if test $v_rev -lt 2
then AC_MSG_ERROR([PolyML version 5.4.2 or later required]);
fi
fi
fi
fi

if test -z "$METIT"
then AC_MSG_NOTICE([no existing metit found]);
fi

#echo "'dirname $METIT'"
#echo "${bindir}"
#echo ${exec_prefix}


AC_CHECK_LIB(gcc, main)
AC_CHECK_LIB(gcc_s, main)
AC_CHECK_LIB(stdc++, main)
AC_CHECK_LIB([gmp], main)
AC_CHECK_LIB([pthread], [pthread_create])
AC_CHECK_LIB(dl, dlopen)
AC_CHECK_LIB(m, floor)

AC_CHECK_LIB([polyml], main, [],
  [AC_MSG_ERROR([Could not find polyml library])])

AC_CHECK_LIB([polymain], main, [],
  [AC_MSG_ERROR([Could not find polymain library])])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT


# look for Z3, qepcad and Mathematica so that
# suggested additions to .bashrc or .profile can be
# made (NB no changes will be made but the
# suggested commands will be echoed to the screen)
AC_ARG_VAR([Z3], [Path to z3])
AC_ARG_VAR([QEPCAD], [Path to qepcad])
AC_ARG_VAR([MATHEMATICA], [Path to the Mathematica kernel])





if test -z $Z3_NONLIN
then
AC_PATH_PROG([Z3],[z3])

if test -z $Z3
then AC_MSG_NOTICE([RCF decision procedure Z3 not found]);
else
AC_MSG_NOTICE([set the following environment variable to allow MetiTarski to find Z3 (eg in .bashrc or .profile) : export Z3_NONLIN=]$Z3);
fi
else
AC_MSG_NOTICE([Z3_NONLIN already set to ]$Z3_NONLIN);
fi

if test -z $qe
then
AC_PATH_PROG([QEPCAD],[qepcad])
if test -z $QEPCAD
then AC_MSG_NOTICE([RCF decision procedure qepcad not found]);
else
read qe_bin_path <<EOF
`dirname $QEPCAD`
EOF
read qe_path <<EOF
`dirname $qe_bin_path`
EOF
AC_MSG_NOTICE([set the following environment variable to allow MetiTarski to find qepcad (eg in .bashrc or .profile) : export qe=]$qe_path);
fi
else
AC_MSG_NOTICE([qe already set to ]$qe);
fi

if test -z $MATH_KERNEL
then
AC_PATH_PROG([MATHEMATICA],[MathKernel])
if test -z $MATHEMATICA
then AC_MSG_NOTICE([RCF decision procedure Mathematica (MathKernel) not found]);
else
AC_MSG_NOTICE([set the following environment variable to allow MetiTarski to find Mathematica's MathKernel (eg in .bashrc or .profile) : MATH_KERNEL=]$MATHEMATICA);
fi
else
AC_MSG_NOTICE([MATH_KERNEL already set to ]$MATH_KERNEL);
fi


