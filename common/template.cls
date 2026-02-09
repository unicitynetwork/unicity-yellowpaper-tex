\ProvidesClass{template}    % commenting this line out avoids a warning if name not given explicitly

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% C L A S S E S     A N D     P A C K A G E S
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Base class, which we will modify
\LoadClass[a4paper, twoside, 12pt, article, draft]{memoir}

% Removes warning about included pdfs
\pdfminorversion=7

% Make the figure and table captions separated by full stops rather than colons.
\usepackage{caption}
\captionsetup[table]{labelsep=period}
\captionsetup[figure]{labelsep=period}

% Margins
\usepackage[top=1in,bottom=1in,left=1in,right=1in,pdftex]{geometry}

% For figuring out, how many pages there are
\usepackage{lastpage}

% We want to do later MakeUppercase for the section heads and when \label{}
% is included in the section head, then it will break everything.
% Textcase package provides more intelligent MakeUppercase command
\usepackage[overload]{textcase}

% utf8 fileformat
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}

% must be before hyperref
\usepackage{imakeidx}

% Cross-references between files, must be before hyperref
% Note that referred files must be compiled first to generate .aux files
\usepackage{xr-hyper}

%  Enables URL formatting, URL breaking and linked entries in the PDF
\usepackage{url}
\usepackage[pdfborder={0 0 0}, pdftex, pdfpagelayout=TwoPageRight, pagebackref=true]{hyperref}
\pdfstringdefDisableCommands{\let\HyPsd@CatcodeWarning\@gobble}  % remove warning

\usepackage{nameref}
\usepackage{zref-xr}
\zxrsetup{
  tozreflabel=false,
  toltxlabel=true,
}

% Graphics and color options
\usepackage{graphicx}
\usepackage{color}

\usepackage{tikz}
\usetikzlibrary{positioning}
\usetikzlibrary{trees}
\usetikzlibrary{automata, arrows}

% For large multi-page tables
\usepackage{longtable}

% Flexible list styles
\usepackage{enumitem}
\setlist[description]{nosep,labelwidth=2em,itemsep=.1ex}

% Puts a frame around a text or other item
\usepackage{framed}

% Math Fonts
\usepackage{amsmath,amssymb}
\usepackage[mathscr]{eucal}
\usepackage{amsthm}

% More flexible tex variables
\usepackage{calc}

% Defining new floating environments
\usepackage{float}

% Draws the DRAFT watermark in every page. Comment this out in the final version
\usepackage{draftwatermark}

\SetWatermarkText{}
\SetWatermarkScale{1}
\SetWatermarkLightness{0.96} % 0.90 is a bit darker
\newcommand{\watermark}[1]{\SetWatermarkText{#1}}

% Times New Roman font for body text
\usepackage{txfonts}

% Arial font for section headlines. The font can be installed
% with ftp://tug.org/tex/getnonfreefonts/install-getnonfreefonts utility
%\usepackage[scaled]{uarial}
\renewcommand*{\familydefault}{\sfdefault}

\newcommand{\TemplateArial}{\fontfamily{phv} \selectfont}

\usepackage{xspace}

% Pseudocode; \Event, \Message blocks
\usepackage{algorithm}
\usepackage{algpseudocode}
\algblockdefx[EVENT]{Event}{EndEvent}%
  [1]{\textbf{on event}\ \texttt{#1}\ \algorithmicdo}%
  {\algorithmicend\ \textbf{on}}
\algblockdefx[MESSAGE]{Message}{EndMessage}%
  [2][msg]{\textbf{upon message}\ <\texttt{#1}\ |\ #2>\ \algorithmicdo}%
  {\algorithmicend\ \textbf{upon}}
\algnewcommand{\NULL}{\textsc{Null}\xspace}
\algnewcommand{\TRUE}{\textsc{True}\xspace}
\algnewcommand{\FALSE}{\textsc{False}\xspace}
\algnewcommand{\Assert}{\textbf{assert}\xspace}
\algnewcommand{\Parse}{\textbf{parse}\xspace}
\MakeRobust{\Call} % for nested Calls

% Git branch and revision number macro
% branch name is adjusted to be a legal filename
\usepackage{xstring}
\usepackage{catchfile}

\IfFileExists{.git/HEAD}%
{%
	\CatchFileDef{\githead}{.git/HEAD}{}
	\StrGobbleRight{\githead}{1}[\gitbranch]
	\StrBehind[2]{\gitbranch}{/}[\gitbranch]
	\IfFileExists{.git/refs/heads/\gitbranch}%
	{\CatchFileDef{\gitcommit}{.git/refs/heads/\gitbranch}{}}%
	{\newcommand{\gitcommit}{\githead/}%  detached head
	\renewcommand{\gitbranch}{<no branch>}%
	}
	\newcommand{\gitrevision}{%
	\StrLeft{\gitcommit}{8}%
	}
}
{%
	\IfFileExists{../.git/HEAD}%
	{%
		\CatchFileDef{\githead}{../.git/HEAD}{}
		\StrGobbleRight{\githead}{1}[\gitbranch]
		\StrBehind[2]{\gitbranch}{/}[\gitbranch]
		\IfFileExists{../.git/refs/heads/\gitbranch}%
		{\CatchFileDef{\gitcommit}{../.git/refs/heads/\gitbranch}{}}%
		{\newcommand{\gitcommit}{\githead/}%  detached head
		\renewcommand{\gitbranch}{<no branch>}%
		}
		\newcommand{\gitrevision}{%
		\StrLeft{\gitcommit}{8}%
		}
	}
	{% not in git repo?
		\newcommand{\gitbranch}{<not in>}%
		\newcommand{\gitrevision}{<git repo>}%
	}
}
\theoremstyle{definition}
\newtheorem{ruledef}{Rule}
\newtheorem*{ruledef*}{Rule}

% ABNF listings
\usepackage{ucs}
\usepackage{listings}
\lstset{
	basicstyle=\tiny\ttfamily,
	breaklines=true,
	breakatwhitespace=true,
	tabsize=2,
	columns=fullflexible,
    texcl=true   % tex in listing comments
}
\lstdefinelanguage{abnf}{
	comment=[l]{;},
	identifierstyle=\bfseries
}

\definecolor{shadecolor}{gray}{0.9}

\usepackage[
    type={CC},
    modifier={by},
    version={4.0},
]{doclicense}

\makeindex

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% D O C U M E N T    S E T T I N G S
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\ProcessOptions\relax

% Document Parameters
\newcommand{\@TemplateStringConfidential}{Confidential}
\newcommand{\@TemplateStringDate}{Date:}
\newcommand{\@TemplateStringDocumentType}{}
\newcommand{\@TemplateStringVersion}{Version}
\newcommand{\@TemplateStringPages}{pages}
\newcommand{\@TemplateStringDocument}{Doc. }
\newcommand{\@TemplateStringBackofTitlePage}{\copyright~Unicity~Labs, \the\year}
\newcommand{\@TemplateStringCopyrightFooter}{\copyright~Unicity~Labs, \the\year}

% Commands for setting the document type, number, version, etc.
\newcommand{\TemplateDefineDocumentType}[1]{\def\@TemplateStringDocumentType{#1}}
\newcommand{\TemplateDefineDocumentNumber}[1]{\def\@TemplateDocumentNumber{#1}}
\newcommand{\TemplateDefineDocumentVersion}[1]{\def\@TemplateDocumentVersion{#1}}
\newcommand{\TemplateDefineDocumentSecurity}[1]{\renewcommand{\@TemplateStringConfidential}{#1}}
\newcommand{\TemplateDefineAcknowledgement}[1]{\def\@TemplateAcknowledgement{#1}}
\newcommand{\TemplateDefineCopyrightFooter}[1]{\renewcommand{\@TemplateStringCopyrightFooter}{#1}}
\newcommand{\TemplateDefineBackofTitlePage}[1]{\renewcommand{\@TemplateStringBackofTitlePage}{#1}}

% .. and initialize them to empty
\TemplateDefineDocumentNumber{}
\global\let\@TemplateDocumentNumber\@empty
\TemplateDefineDocumentVersion{}
\global\let\@TemplateDocumentVersion\@empty
\TemplateDefineAcknowledgement{}
\global\let\@TemplateAcknowledgement\@empty

% Pagestyle with headers and footers
\setlength{\headwidth}{\textwidth}
\makepagestyle{TemplateFancy}
\makerunningwidth{TemplateFancy}{\headwidth}

% No indent of paragraphs
\setlength{\parindent}{0pt}
\setlength{\parskip}{1.5ex}

% Confidentiality mark in the headers
\makeoddhead{TemplateFancy}{}{}{
	\TemplateArial \tiny \@TemplateStringConfidential}
\makeevenhead{TemplateFancy}{}{}{
	\TemplateArial \tiny \@TemplateStringConfidential}

% Odd footers
\makeoddfoot{TemplateFancy}{
	\TemplateArial
	{\tiny\@date}}
	{}
	{\TemplateArial
	{\tiny\thepage\ / \pageref*{LastPage}}}

% Even footers
\makeevenfoot{TemplateFancy}{
	\TemplateArial
	{\tiny\@date}}
	{}
	{\TemplateArial
	{\tiny\thepage\ / \pageref*{LastPage}}}

% Footer rule
\makefootrule{TemplateFancy}{\headwidth}{\normalrulethickness}{0pt}

% We have multiline headers, therefore less space is available for text.
\addtolength{\footskip}{2mm}

% Enforce pagestyle for pages with new chapters as well
\aliaspagestyle{chapter}{TemplateFancy}

% Set the new style as the default
\pagestyle{TemplateFancy}

% Titlepage style with headings
\makepagestyle{TemplateTitle}
\makerunningwidth{TemplateTitle}{\headwidth}
% \makeoddhead{TemplateTitle}{
% 	\begin{minipage}[t]{0.5\textwidth}
% 		\hspace{-7mm}
% 		%\includegraphics[width=90mm]{templatelogo.png}
% 	\end{minipage}
% 	}{}{
% 	\raisebox{2.5mm}[0mm]{\TemplateArial \scriptsize \bfseries \@TemplateStringConfidential}
% 	}

% Chapter and section headline style
\renewcommand{\printchapternum}{\LARGE \bfseries \TemplateArial \thechapter}
\renewcommand{\printchaptertitle}[1]{\LARGE \bfseries \TemplateArial #1}
\setlength{\beforechapskip}{60pt}
\setlength{\afterchapskip}{40pt}

\let\stdchapter\chapter
\renewcommand\chapter{\clearpage\ \stdchapter}

\setsecheadstyle{\normalsize \bfseries \TemplateArial}
\setsubsecheadstyle{\normalsize \bfseries \TemplateArial}
\setsubsubsecheadstyle{\TemplateArial}

% Make dots appear in the table of contents also for chapters
\renewcommand{\cftchapterdotsep}{\cftdotsep}
\addtolength{\cftsubsectionnumwidth}{0.5em}
\addtolength{\cftsubsubsectionindent}{0.5em}

% make enumerate and itemize lists tighter
\firmlists

% and change the numbering for nested lists
\renewcommand{\labelenumi}{\arabic{enumi}.}
\renewcommand{\labelenumii}{\arabic{enumi}.\arabic{enumii}}
\renewcommand{\labelenumiii}{\arabic{enumi}.\arabic{enumii}.\arabic{enumiii}}
\renewcommand{\labelenumiv}{\arabic{enumi}.\arabic{enumii}.\arabic{enumiii}.\arabic{enumiv}}

% make LaTeX observe right margins at all costs:
\sloppy

% Numbering of parts and presenting them in the table of contents
\setcounter{secnumdepth}{3}  % Numbering depth
\setcounter{tocdepth}{3}     % Table of contents depth

% Draft editing remark macros
\newcommand{\todo}[1]{\textcolor{blue}{[\textbf{TODO}: #1]}}
\newcommand{\comm}[2]{\textcolor{red}{[\textbf{#1}: #2]}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% T I T L E   P A G E
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand{\maketitle}{%
	\thispagestyle{TemplateTitle}

	\begin{minipage}[t]{0.5\textwidth}
		\vspace{-6.5mm}
		\hfill
	\end{minipage}
	\vspace{4cm}
	\begin{flushleft}
		\TemplateArial
		{\huge \bfseries \@title}
		\vskip 1cm
		{\large\bfseries \theauthor}

		\vfill

		{\large \bfseries
			\@TemplateStringDocumentType

			\ifx\@TemplateDocumentVersion\@empty
			Document version undefined, use the TemplateDefineDocumentVersion command!
			\else
			\@TemplateStringVersion~\@TemplateDocumentVersion
			\fi

			\@date

			\@TemplateStringCopyrightFooter
			\doclicenseThis

		}\par
		% \vspace{2cm}
		{\scriptsize \@TemplateAcknowledgement}
	\end{flushleft}
	\pagebreak
}
