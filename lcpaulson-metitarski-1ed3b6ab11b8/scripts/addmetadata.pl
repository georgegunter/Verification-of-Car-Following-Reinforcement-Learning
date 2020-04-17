#!/usr/bin/perl -w
#Inputs:  1. A directory of problems in TPTP format (given by --indir <dir>)
#         2. The name of the output directory (given by --outdir <dir>)
#         3. A CSV file containing metadata (currently, just the number of Skolem constants)
#Action: adds metadata to each problem.

use strict;
use Getopt::Long;
use File::Slurp;

my ($indir, $outdir, $csv);
my $replace = 0;          # if set, allows overwriting of the output directory

GetOptions ('indir=s' => \$indir, 'outdir=s' => \$outdir, 'csv=s' => \$csv, 'replace' => \$replace)
 or die "usage: --indir <dir> --outdir <dir> --csv <file> --replace\n";

unless (-d $indir) { die "invalid input directory $indir\n" }
unless (defined ($outdir)) { die "must specify the output directory, using --out <dir>\n" }
unless (defined ($csv)) { die "must specify the csv file, using --csv <dir>\n" }
if ($indir eq $outdir) { die "the input and output directories must be different\n" }

#Read the entire contents of the metadata file into a string.
my $csvtext = read_file($csv)
   or die "\nFATAL ERROR:\nUnable to open the input file $csv: $!";

my $divline = "%--------------------------------------------------------------------------\n";

opendir INDIR, $indir or die "\nFATAL ERROR:\nUnable to open the directory $indir: $!";

mkdir "$outdir", 0755 or $replace or die "Can't make directory $outdir: $!\n";

foreach my $file (readdir INDIR) {
  my $filepath = "$indir/$file";
  next unless (-f $filepath and ($file =~ /\.p/ or $file =~ /\.tptp/));
  next if (substr($file,0,1) eq ".");   #ignore invisible files
  my $filepat = "\"$file\"";
  #deal with regexp metacharacters in filenames
  $filepat =~ s/\+/\\+/g;  $filepat =~ s/\./\\./g;
  my $pattern = "$filepat,\\d+,(\\d+),\\d+";
  my $nvars = "UNKONWN";
  if ($csvtext =~ /$pattern/) {
    $nvars = $1;
  } else {
    print "$file: UNKONWN, $pattern\n";
  }
  my $infiletext = read_file($filepath)
     or die "\nFATAL ERROR:\nUnable to open the input file $filepath: $!";
  open OUTFILE, ">$outdir/$file";
  print OUTFILE
    $divline,
    "% File     : $file\n",
##    "% Status   : Unknown\n",
    "% Syntax   : Number of Skolem constants\t:    $nvars\n",
    "% Source   :\n",
    "% Comments :\n",
    $divline,
    $infiletext;
  close OUTFILE;
}

#   open INFILE, "$filepath" or die "unable to open the input file $filepath: $!";
#   my @localaxioms = ();
#   foreach (<INFILE>) {
#     if (/^\s*include\s*\(\s*'([^'()]*)' *\)\s*\.\s*$/) {
#       print " $1";
#       @localaxioms = (@localaxioms,"%%%%AXIOMS INCLUDED FROM $tptp/$1\n",<AXFILE>, "\n");
#     } else {
#       print OUTFILE;
#     }
#   }
#   close INFILE;
#   print OUTFILE "\n", @axioms, @localaxioms;

