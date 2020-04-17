#!/usr/bin/perl -w
#Inputs:  1. A directory of problems in TPTP format (given by --indir <dir>)
#         2. The name of the output directory (given by --outdir <dir>)
#         3. The name of the base TPTP directory, whence included files are sought
#         4. Axiom files on the standard input (possibly more than one)
#Action: copy problems from indir to outdir, appending the axioms to each.

use strict;
use Getopt::Long;

my ($indir, $outdir);
my $tptp = $ENV{"TPTP"};  # As usual, the default setting comes from the environment variable.
my $replace = 0;          # if set, allows overwriting of the output directory

my $current_date = localtime;
my ($sec,$min,$hour,$mday,$mon,$year) = localtime; 
my $yyyymmdd = sprintf "%4d-%02d-%02d", $year+1900, $mon+1, $mday;

my $command = "% $yyyymmdd: addaxioms.pl @ARGV";

GetOptions ('indir=s' => \$indir, 'outdir=s' => \$outdir, 'tptp=s' => \$tptp, 'replace' => \$replace) 
 and defined ($indir) and defined ($outdir)
 or die "usage: --indir <dir> --outdir <dir> [--tptp <dir>] --replace  <axiom-file> ...  <axiom-file>\n";

unless (-d $indir) { die "invalid input directory $indir\n" }
unless (defined ($outdir)) { die "must specify the output directory, using --out <dir>\n" }
if ($indir eq $outdir) { die "the input and output directories must be different\n" }

unless (defined($tptp)) { die "The TPTP environment variable is unset and --tptp was not given.\n" }
unless (-d $tptp) { die "Invalid TPTP directory $tptp\n" }

my @axioms = ();

#Accumulate the contents of the axiom files listed on the command line.
foreach my $axfile (@ARGV) {
  print "Reading axiom file $axfile\n";
  open AXFILE, "$axfile" or die "\nFATAL ERROR:\nUnable to open the input file $axfile: $!";
  @axioms = (@axioms,"%%%%AXIOMS FROM $axfile\n",<AXFILE>, "\n");   
  close AXFILE;
}

opendir INDIR, $indir or die "\nFATAL ERROR:\nUnable to open the directory $indir: $!";

mkdir "$outdir", 0755 or $replace or die "Can't make directory $outdir: $!\n";

foreach my $file (readdir INDIR) {
  my $filepath = "$indir/$file";
  next unless (-f $filepath and ($file =~ /\.p/ or $file =~ /\.tptp/));
  next if (substr($file,0,1) eq ".");   #ignore invisible files
  print "$filepath:";
  open INFILE, "$filepath" or die "unable to open the input file $filepath: $!";
  open OUTFILE, ">$outdir/$file";
  print OUTFILE $command, "\n";
  my @localaxioms = ();
  foreach (<INFILE>) {
    last if /%%%%AXIOMS/;  #removes any existing axioms added by this script
    if (/^\s*include\s*\(\s*'([^'()]*)' *\)\s*\.\s*$/) {
      print " $1";
      open AXFILE, "$tptp/$1" or die "\nFATAL ERROR:\nUnable to open the input file $tptp/$1: $!";
      @localaxioms = (@localaxioms,"%%%%AXIOMS INCLUDED FROM $tptp/$1\n",<AXFILE>, "\n");   
      close AXFILE;
    } else {
      print OUTFILE;
    }
  }
  close INFILE;
  print OUTFILE "\n", @axioms, @localaxioms;
  close OUTFILE;
  print "*** NO AXIOMS INSERTED***" if (@localaxioms == 0);
  print "\n";
}

