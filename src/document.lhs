\documentclass[a4paper,UKenglish,cleveref, autoref, thm-restate]{oasics-v2021}

%for A4 paper format use option "a4paper", for US-letter use option "letterpaper"
%for british hyphenation rules use option "UKenglish", for american hyphenation rules use option "USenglish"
%for section-numbered lemmas etc., use "numberwithinsect"
%for enabling cleveref support, use "cleveref"
%for enabling autoref support, use "autoref"
%for anonymousing the authors (e.g. for double-blind review), add "anonymous"
%for enabling thm-restate support, use "thm-restate"
%for enabling a two-column layout for the author/affilation part (only applicable for > 6 authors), use "authorcolumns"
%for producing a PDF according the PDF/A standard, add "pdfa"

\usepackage{mathtools}
\usepackage{stmaryrd}
\usepackage{wasysym}

%\pdfoutput=1 %uncomment to ensure pdflatex processing (mandatatory e.g. to submit to arXiv)
%\hideOASIcs %uncomment to remove references to OASIcs series (logo, DOI, ...), e.g. when preparing a pre-final version to be uploaded to arXiv or another public repository

\bibliographystyle{plainurl}% the mandatory bibstyle

\makeatletter
\newcommand{\crefnames}[3]{%
  \@@for\next:=#1\do{%
    \expandafter\crefname\expandafter{\next}{#2}{#3}%
  }%
}
\makeatother

\crefnames{section}{\S}{\S\S}

\setlength{\parskip}{0em} 
\setlength\mathindent{0.2cm}

%% Title information
\title{Renamingless Capture-Avoiding Substitution for Definitional Interpreters}

%% Author with single affiliation.
\author{Casper {Bach Poulsen}}{Delft University of Technology, Netherlands \and \url{http://www.casperbp.net} }{c.b.poulsen@@tudelft.nl}{https://orcid.org/0000-0003-0622-7639}{}%TODO mandatory, please use full name; only 1 author per \author macro; first two parameters are mandatory, other parameters can be empty. Please provide at least the name of the affiliation and the country. The full address is optional. Use additional curly braces to indicate the correct name splitting when the last name consists of multiple name parts.
%
\authorrunning{C. Bach Poulsen}
% First names are abbreviated in the running head.
% If there are more than two authors, 'et al.' is used.

\Copyright{Jane Open Access and Joan R. Public} %TODO mandatory, please use full first names. LIPIcs license is "CC-BY";  http://creativecommons.org/licenses/by/3.0/

% \begin{CCSXML}
% <ccs2012>
%    <concept>
%        <concept_id>10011007.10011006.10011039.10011311</concept_id>
%        <concept_desc>Software and its engineering~Semantics</concept_desc>
%        <concept_significance>500</concept_significance>
%        </concept>
%    <concept>
%        <concept_id>10003752.10003790.10002990</concept_id>
%        <concept_desc>Theory of computation~Logic and verification</concept_desc>
%        <concept_significance>300</concept_significance>
%        </concept>
%  </ccs2012>
% \end{CCSXML}
 
\ccsdesc[500]{Software and its engineering~Semantics}
\ccsdesc[300]{Theory of computation~Logic and verification}

\keywords{Capture-avoiding substitution, Untyped lambda calculus, Definitional interpreter} %TODO mandatory; please add comma-separated list of keywords

%\category{} %optional, e.g. invited paper

%\relatedversion{} %optional, e.g. full version hosted on arXiv, HAL, or other respository/website
%\relatedversiondetails[linktext={opt. text shown instead of the URL}, cite=DBLP:books/mk/GrayR93]{Classification (e.g. Full Version, Extended Version, Previous Version}{URL to related version} %linktext and cite are optional

%\supplement{}%optional, e.g. related research data, source code, ... hosted on a repository like zenodo, figshare, GitHub, ...
%\supplementdetails[linktext={opt. text shown instead of the URL}, cite=DBLP:books/mk/GrayR93, subcategory={Description, Subcategory}, swhid={Software Heritage Identifier}]{General Classification (e.g. Software, Dataset, Model, ...)}{URL to related version} %linktext, cite, and subcategory are optional

%\funding{(Optional) general funding statement \dots}%optional, to capture a funding statement, which applies to all authors. Please enter author specific funding statements as fifth argument of the \author macro.

%\acknowledgements{I want to thank \dots}%optional

%\nolinenumbers %uncomment to disable line numbering

%Editor-only macros:: begin (do not touch as author)%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\EventEditors{John Q. Open and Joan R. Access}
\EventNoEds{2}
\EventLongTitle{42nd Conference on Very Important Topics (CVIT 2016)}
\EventShortTitle{CVIT 2016}
\EventAcronym{CVIT}
\EventYear{2016}
\EventDate{December 24--27, 2016}
\EventLocation{Little Whinging, United Kingdom}
\EventLogo{}
\SeriesVolume{42}
\ArticleNo{23}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt

\begin{document}

\maketitle

\begin{abstract}
  Substitution is a common and popular approach to implementing name binding in definitional interpreters.
  A common pitfall of implementing substitution functions is \emph{variable capture}.
  The traditional approach to avoiding variable capture is to rename variables.
  However, traditional renaming makes for an inefficient interpretation strategy.
  Furthermore, for applications where partially-interpreted terms are user facing it can be confusing if names in uninterpreted parts of the program have been changed.
  In this paper we explore two techniques for implementing capture avoiding substitution in definitional interpreters to avoid renaming.
\end{abstract}


\input{sections/1-introduction.tex}
%include sections/2-interpretation.lhs
%include sections/3-shifting.lhs
\input{sections/4-discussion.tex}

% \input{sections/1-introduction.tex}
% \input{sections/2-interpretation.tex}
% \input{sections/3-normalization.tex}
% \input{sections/4-discussion.tex}


%% Bibliography
\bibliography{references}



%% Appendix
%% \appendix
%% \section{Appendix}
%% 
%% Text of appendix \ldots
%% 
\end{document}
