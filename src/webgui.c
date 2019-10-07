/**********************************************************************************/
/* Copyright (c) 2017, Christopher Deotte                                         */
/*                                                                                */
/* Permission is hereby granted, free of charge, to any person obtaining a copy   */
/* of this software and associated documentation files (the "Software"), to deal  */
/* in the Software without restriction, including without limitation the rights   */
/* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell      */
/* copies of the Software, and to permit persons to whom the Software is          */
/* furnished to do so, subject to the following conditions:                       */
/*                                                                                */
/* The above copyright notice and this permission notice shall be included in all */
/* copies or substantial portions of the Software.                                */
/*                                                                                */
/* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR     */
/* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,       */
/* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE    */
/* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER         */
/* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,  */
/* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE  */
/* SOFTWARE.                                                                      */
/**********************************************************************************/

/***************************************************************************/
/* WEBGUI A web browser based graphical user interface                     */
/* Version: 1.0 - June 25 2017                                             */
/***************************************************************************/
/* Author: Christopher Deotte                                              */
/* Advisor: Randolph E. Bank                                               */
/* Funding: NSF DMS-1345013                                                */
/* Documentation: http://ccom.ucsd.edu/~cdeotte/webgui                     */
/***************************************************************************/

#include<netinet/in.h>
#include<stdio.h>
#include<stdlib.h>
#include<sys/socket.h>
#include<sys/stat.h>
#include<sys/types.h>
#include<unistd.h>
#include<string.h>
#include<ctype.h>
#include<pthread.h>
#include<dirent.h>
#include<sys/time.h>
#include<errno.h>

static int cmdct, nct;
static const int maxnamelen=20, maxabbrlen=3, maxdeftlen=40;
static const int maxwebpage=100000;
static char **cmdn, **cmda, **cmdt;
static char **nn, **na, **nd, *nt;
static int **cmdp, *cmdpct, *cmdc;
static int *no, *nu, *nw, *ni;
static const int maxlines = 100, maxhistory=100;
static int indexA = 0, indexB = 0, bufferwaitA = 0, bufferwaitB = 0;
static char *bufferA, *bufferB; //maintained as Fortran strings (space padded)
static char **history; //maintained as C strings (null terminated)
static char *webpageA=NULL, *webpageB="";
static char *webpageC, *webpageD, title[81]="";
static int animate = 0;
static int load_webpageC_from_file = 0;
static int load_pngs_from_file = 0;
static int initialized=0, init0=0, running=0, hindex=0, waiting=0;
static char **usrlist; //maintained as Fortran strings
static unsigned char **colors[3]={NULL,NULL,NULL};
static int ncolor[3]={0,0,0};
static unsigned char *bitmap[3]={NULL,NULL,NULL};
static int bitmaplen[3]={0,0,0};
static float **colorsGL[3]={NULL,NULL,NULL};
static int ncolorGL[3]={0,0,0};
static int starttri = 1000, maxtri=0;
static int startlin = 1000, maxlin=0;
static float **triangles[3]={NULL,NULL,NULL};
static float **lines[3]={NULL,NULL,NULL};
static int indexT[3]={0,0,0}, indexL[3]={0,0,0};
static int tricount[3][10]={{0}};
static int ccount[3][10]={{0}};
static int cframe=1, cpane=-1, usrlen=0;
static int sg[3]={-1,-1,-1}, pic[3]={-1,-1,-1};
static char *databuffer=NULL;
static int webGLendian=0, dbpreamble[3][20]={{0}};
static int query=-1, query2=-1;
static unsigned char firewall[8]={0,0,0,0,0,0,0,0};
static int stopthread = 0;
static struct timeval started;
static int create_socket;
static int lock[6]={0,0,0,0,0,0}, lock2[6]={0,0,0,0,0,0};
static struct sockaddr_in address;
static pthread_t pth;

/* external FORTRAN interface routines */
/* call these without the underscore */
/* fortran passes arguments by reference */
extern void webinit0_(char *str, int *len, int *iu, double *ru, char *su);
extern void webinit_(char *str, int *len);
extern int webstart_(int *x);
extern void webstop_();
extern void webreadline_(char *str);
extern void webwriteline_(char *str);
extern void webupdate_(int *ip, double *rp, char *sp);
extern void webupdate2_(int *ip, double *rp, char *sp, int *iu, double *ru, char *su);
extern void webupdate3_(int *iu, double *ru, char *su);
extern void websettitle_(char *str, int len);
extern int webquery_();
extern void websetcolors_(int* nc, double* red, double* green, double* blue, int* ipane);
extern void webimagedisplay_(int* nx, int* ny, int* image, int* ipane);
extern void webframe_(int* iframe);
extern void webfillflt_(float* x, float* y, float* z, int* n, int* icolor);
extern void weblineflt_(float* x, float* y, float* z, int* n, int* icolor);
extern void webfilldbl_(double* x, double* y, double* z, int* n, int* icolor);
extern void weblinedbl_(double* x, double* y, double* z, int* n, int* icolor);
extern void webgldisplay_(int* ipane);
extern void webbutton_(int *highlight, char *cmd, int cmdlen);
extern void webpause_();
extern void websetmode_(int* x);

/* external C interface routines */
extern void webinit(char *str, int len);
extern int webstart(int x);
extern void webstop();
extern void webreadline(char *str);
extern void webwriteline(char *str);
extern void webupdate(int *ip, double *rp, char *sp);
extern void websettitle(char *str);
extern int webquery();
extern void websetcolors(int nc, double* red, double* green, double* blue, int ipane);
extern void webimagedisplay(int nx, int ny, int* image, int ipane);
extern void webframe(int iframe);
extern void webfillflt(float* x, float* y, float* z, int n, int icolor);
extern void weblineflt(float* x, float* y, float* z, int n, int icolor);
extern void webfilldbl(double* x, double* y, double* z, int n, int icolor);
extern void weblinedbl(double* x, double* y, double* z, int n, int icolor);
extern void webgldisplay(int ipane);
extern void webbutton(int highlight, char *cmd);
extern void webpause();
extern void websetmode(int x);

/* internal routines */
void *startlisten(void *arg);
void webwritenline(char *str, int n);
void shrinkBuffer();
void parse(char *str, char *key, char *value);
void updatedeft(char *cmd);
void updatewebpageA(int hide);
void updatewebpageC();
void updatewebpageD(int xtra);
void updatewebpageD2(int x, int xtra);
void allupdate();
void updatedatabuffer(int x, int xtra);
int updatedatabuffer3(int x, int endian);
int countskips(int len);
void listfiles(char *str);
void pushcanvas(char *str);
void setquery(char *str);
void setendian(char *str);
void setanimate(char *str);
void setfirewall(char *str, unsigned char *ip);
void releaseWebGL(char *str);
int growtri(int x, int shrink);
int growlin(int x, int shrink);
void getdeftbyname(char *name, char *deft, char *abbr, int *nopt, int *index);
void getdeftbyindex(char *name, char *deft, char *abbr, int *nopt, int index);
int getindexbyname(char *name);
int getindexbycmd(char *name);
void remove0e(char *str);
void c2fortran(char* str, int len);
void fortran2c(char *str, int len, int quote);
void removespaces(char *str, int size);
void removeapost(char *str);
void fixquotes(char *dst, char *src);
void urldecode(char *dst, const char *src);
int str2int(char* str);
int power(int x, int y);
int ispng(char* str);
int isint(char *str);
int isreal(char *str);
int isvalid(int x, char c);
unsigned long fsize(char* file);

/* PNG image files */
static unsigned char folderpng[446] = {137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 19, 0, 0, 0, 17, 8, 2, 0, 0, 0, 176, 250, 0, 144, 0, 0, 0, 9, 112, 72, 89, 115, 0, 0, 14, 195, 0, 0, 14, 195, 1, 199, 111, 168, 100, 0, 0, 0, 9, 116, 69, 88, 116, 67, 111, 109, 109, 101, 110, 116, 0, 0, 137, 42, 141, 6, 0, 0, 1, 91, 73, 68, 65, 84, 120, 156, 99, 248, 79, 46, 96, 24, 80, 157, 103, 102, 154, 156, 158, 97, 124, 114, 154, 225, 241, 41, 250, 247, 239, 223, 255, 246, 237, 27, 81, 58, 129, 218, 144, 69, 15, 245, 107, 157, 56, 113, 2, 191, 102, 6, 36, 109, 51, 145, 208, 255, 189, 93, 170, 187, 218, 149, 182, 183, 200, 111, 109, 146, 221, 220, 40, 189, 161, 78, 2, 232, 144, 239, 223, 191, 163, 232, 4, 58, 242, 255, 247, 137, 255, 191, 244, 161, 32, 84, 176, 174, 70, 172, 167, 167, 231, 222, 189, 123, 40, 58, 129, 126, 251, 255, 186, 245, 255, 179, 198, 163, 147, 116, 209, 208, 129, 94, 141, 61, 157, 42, 59, 90, 21, 182, 52, 202, 0, 109, 6, 34, 160, 205, 8, 157, 192, 32, 249, 255, 160, 26, 168, 14, 95, 128, 60, 107, 4, 18, 139, 11, 185, 129, 54, 35, 116, 130, 244, 92, 201, 7, 251, 118, 38, 46, 244, 227, 104, 2, 144, 92, 144, 199, 145, 151, 151, 135, 208, 9, 12, 201, 255, 103, 210, 65, 190, 5, 42, 2, 122, 24, 27, 122, 191, 39, 28, 40, 59, 47, 135, 45, 55, 55, 23, 161, 19, 232, 25, 160, 78, 176, 107, 103, 130, 60, 140, 13, 61, 219, 236, 7, 148, 157, 147, 197, 130, 162, 19, 24, 1, 64, 157, 251, 123, 212, 65, 58, 31, 84, 99, 69, 119, 86, 186, 0, 101, 103, 101, 48, 161, 232, 4, 198, 27, 80, 39, 48, 0, 65, 58, 175, 228, 99, 69, 151, 23, 88, 3, 101, 103, 166, 51, 34, 252, 249, 230, 211, 119, 96, 64, 195, 163, 27, 24, 111, 171, 43, 133, 87, 148, 9, 44, 45, 230, 5, 134, 36, 48, 72, 128, 126, 3, 58, 18, 104, 27, 80, 155, 143, 143, 79, 115, 115, 51, 194, 78, 96, 42, 3, 166, 53, 160, 80, 46, 33, 0, 84, 3, 84, 137, 208, 9, 209, 12, 180, 249, 26, 33, 128, 156, 19, 0, 169, 153, 11, 97, 9, 86, 0, 45, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130};

static unsigned char uppng[472] = {137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 19, 0, 0, 0, 17, 8, 2, 0, 0, 0, 176, 250, 0, 144, 0, 0, 0, 9, 112, 72, 89, 115, 0, 0, 14, 195, 0, 0, 14, 195, 1, 199, 111, 168, 100, 0, 0, 0, 9, 116, 69, 88, 116, 67, 111, 109, 109, 101, 110, 116, 0, 0, 137, 42, 141, 6, 0, 0, 1, 117, 73, 68, 65, 84, 120, 156, 99, 248, 79, 46, 96, 24, 80, 157, 103, 102, 154, 156, 158, 97, 124, 114, 154, 225, 241, 41, 250, 247, 239, 223, 255, 246, 237, 27, 81, 58, 129, 218, 144, 69, 15, 245, 107, 157, 56, 113, 2, 191, 102, 6, 36, 109, 51, 145, 208, 255, 189, 93, 170, 187, 218, 149, 182, 183, 200, 111, 109, 146, 221, 220, 40, 189, 161, 78, 2, 232, 144, 239, 223, 191, 163, 232, 4, 58, 242, 255, 247, 137, 255, 191, 244, 193, 17, 3, 3, 186, 255, 215, 213, 136, 245, 244, 244, 220, 187, 119, 15, 69, 39, 208, 111, 255, 95, 183, 254, 127, 214, 120, 116, 146, 46, 16, 49, 192, 0, 144, 125, 160, 87, 99, 79, 167, 202, 142, 86, 133, 45, 141, 50, 64, 155, 129, 8, 104, 51, 66, 39, 48, 72, 254, 63, 168, 6, 170, 3, 241, 81, 1, 194, 210, 103, 141, 64, 98, 113, 33, 55, 208, 102, 132, 78, 144, 158, 43, 249, 96, 223, 66, 253, 9, 214, 131, 236, 237, 153, 63, 142, 38, 0, 201, 5, 121, 28, 121, 121, 121, 8, 157, 192, 144, 252, 127, 38, 29, 228, 91, 160, 34, 160, 135, 191, 79, 4, 233, 4, 51, 224, 232, 253, 158, 112, 160, 236, 188, 28, 182, 220, 220, 92, 132, 78, 160, 103, 128, 58, 193, 174, 157, 9, 242, 240, 235, 86, 116, 55, 191, 110, 125, 182, 217, 15, 40, 59, 39, 139, 5, 69, 39, 48, 2, 128, 58, 247, 247, 168, 131, 116, 62, 168, 198, 138, 238, 172, 116, 1, 202, 206, 202, 96, 66, 209, 9, 140, 55, 160, 78, 96, 0, 130, 116, 94, 201, 199, 138, 46, 47, 176, 6, 202, 206, 76, 103, 68, 248, 243, 205, 167, 239, 192, 128, 134, 71, 55, 48, 222, 86, 87, 10, 175, 40, 19, 88, 90, 204, 11, 12, 73, 96, 144, 0, 253, 6, 116, 36, 208, 54, 160, 54, 31, 31, 159, 230, 230, 102, 132, 157, 192, 84, 6, 76, 107, 64, 161, 92, 66, 0, 168, 6, 168, 18, 37, 221, 2, 53, 3, 109, 190, 70, 8, 32, 231, 4, 0, 48, 59, 228, 11, 224, 190, 98, 9, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130};

static unsigned char filepng[402] = {137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 19, 0, 0, 0, 17, 8, 2, 0, 0, 0, 176, 250, 0, 144, 0, 0, 0, 9, 112, 72, 89, 115, 0, 0, 14, 195, 0, 0, 14, 195, 1, 199, 111, 168, 100, 0, 0, 1, 68, 73, 68, 65, 84, 120, 156, 173, 207, 49, 75, 195, 64, 20, 7, 240, 126, 37, 191, 128, 131, 171, 131, 159, 192, 201, 73, 172, 109, 179, 148, 184, 180, 34, 71, 55, 161, 166, 46, 1, 117, 49, 149, 42, 100, 147, 22, 211, 54, 109, 176, 72, 12, 38, 214, 216, 138, 18, 18, 210, 44, 54, 216, 33, 49, 173, 13, 154, 162, 15, 110, 113, 72, 81, 15, 143, 199, 227, 224, 189, 31, 255, 187, 196, 39, 233, 73, 252, 167, 20, 15, 86, 122, 173, 229, 226, 198, 66, 185, 176, 8, 151, 253, 220, 26, 116, 148, 218, 60, 220, 89, 53, 77, 51, 12, 195, 120, 169, 170, 207, 52, 45, 65, 129, 108, 156, 237, 237, 110, 165, 47, 170, 247, 167, 197, 180, 120, 46, 128, 172, 84, 42, 195, 225, 48, 94, 210, 116, 187, 115, 229, 20, 214, 151, 220, 241, 43, 244, 209, 219, 24, 250, 244, 227, 29, 58, 76, 41, 138, 178, 44, 107, 174, 172, 171, 93, 96, 184, 64, 250, 225, 20, 100, 52, 155, 97, 9, 15, 158, 43, 165, 219, 7, 66, 217, 210, 250, 96, 114, 249, 60, 174, 122, 179, 249, 107, 169, 246, 9, 51, 197, 238, 221, 247, 76, 28, 139, 167, 63, 73, 181, 71, 250, 79, 229, 145, 48, 83, 210, 158, 8, 51, 27, 55, 61, 156, 9, 81, 127, 147, 85, 69, 195, 129, 47, 147, 96, 52, 25, 119, 148, 235, 166, 36, 29, 159, 148, 153, 82, 137, 101, 89, 199, 113, 226, 165, 239, 251, 237, 75, 237, 136, 227, 182, 17, 74, 101, 50, 201, 100, 50, 155, 205, 34, 132, 24, 134, 225, 56, 78, 150, 101, 207, 243, 226, 101, 20, 69, 182, 109, 215, 106, 53, 158, 231, 5, 65, 128, 85, 93, 215, 13, 195, 24, 12, 6, 174, 235, 6, 65, 0, 11, 120, 243, 11, 53, 195, 70, 162, 55, 207, 82, 20, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130};

/* C wrappers of Fortran functions */
int webstart(int x){
    return webstart_(&x);
}
void webreadline(char *str){
    return webreadline_(str);
}
void webwriteline(char *str){
    return webwriteline_(str);
}
void webinit(char *str, int len){
    return webinit_(str,&len);
}
void webupdate(int *ip, double *rp, char *sp){
    return webupdate_(ip,rp,sp);
}
void websettitle(char *str){
    return websettitle_(str,(int)strlen(str));
}
void webstop(){
    return webstop_();
}
void websetcolors(int nc, double* red, double* green, double* blue, int ipane){
    return websetcolors_(&nc,red,green,blue,&ipane);
}
void webimagedisplay(int nx, int ny, int* image, int ipane){
    return webimagedisplay_(&nx,&ny,image,&ipane);
}
void webframe(int iframe){
    return webframe_(&iframe);
}
void webfillflt(float* x, float* y, float* z, int n, int icolor){
    return webfillflt_(x,y,z,&n,&icolor);
}
void weblineflt(float* x, float* y, float* z, int n, int icolor){
    return weblineflt_(x,y,z,&n,&icolor);
}
void webfilldbl(double* x, double* y, double* z, int n, int icolor){
    return webfilldbl_(x,y,z,&n,&icolor);
}
void weblinedbl(double* x, double* y, double* z, int n, int icolor){
    return weblinedbl_(x,y,z,&n,&icolor);
}
void webgldisplay(int ipane){
    return webgldisplay_(&ipane);
}
int webquery(){
    return webquery_();
}
void webbutton(int highlight, char *cmd){
    return webbutton_(&highlight,cmd,(int)strlen(cmd));
}
void webpause(){
    return webpause_();
}
void websetmode(int x){
    return websetmode_(&x);
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webinit0_(char *str, int *len, int *iu, double *ru, char *su){
    /* PLTMG calls this before webinit_ to init usrcmd parameter list */
    /* str and len are same structure as described by webinit_ */
    
    if (init0==1 || initialized==1) {
        printf("webgui: WARNING: cannot call webinit0 twice, ignoring call\n");
        return;
    }
    init0 = 1;
    query = 2;
    int i, sct;
    char name[81], deft[81], abbr[81], value[81];
    nct = 0; sct = 0;
    for (i=0; i<*len; i++){
        if (str[i*80]=='n') nct++;
        if (str[i*80]=='s') sct++;
        c2fortran(str+i*80,80);
        removespaces(str+i*80,80);
    }
    usrlist = (char**)malloc((sct+2*nct)*sizeof(char*));
    for (i=0; i<sct+2*nct; i++)
    usrlist[i] = (char*)malloc(80);
    usrlen=0;
    for (i=0; i<*len; i++){
        if (str[i*80]=='n'){
            parse(str+i*80+1,"n",name);
            parse(str+i*80+1,"t",abbr);
            parse(str+i*80+1,"d",deft);
            parse(str+i*80+1,"i",value);
            strncpy(usrlist[usrlen++],str+i*80,80);
            if (deft[0]=='\0' && abbr[0]=='i')
                sprintf(usrlist[usrlen-1]+60,",d=%d ",iu[str2int(value)-1]);
            if (deft[0]=='\0' && abbr[0]=='r')
                sprintf(usrlist[usrlen-1]+60,",d=%.1f ",ru[str2int(value)-1]);
            sprintf(usrlist[usrlen++],"r c=usrcmd,n=%s",name);
        }
        else if (str[i*80]=='s')
        strncpy(usrlist[usrlen++],str+i*80,80);
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webinit_(char *str, int *len){
    /* Call this before webstart_ to create buttons */
    /* where str is an array of strings as char[len][80] */
    /* with either space terminated or null terminated strings. */
    /* Read manual for formatting description. */
    /* If you don't call this, you'll get a generic command window */
    /* without buttons. */
    
    if (initialized==1) {
        printf("webgui: WARNING: cannot call webinit twice, ignoring call\n");
        return;
    }
    initialized=1;
    query = 2;
    int count=0, nopt=0, i, j, k, tmp=0;
    int *len2 = &tmp;
    if (init0==1){
        char *str2;
        str2 = (char*)malloc((*len+usrlen)*80);
        for (i=0;i<*len*80;i++) str2[i]=str[i];
        for (i=0;i<usrlen;i++) for (j=0;j<80;j++)
        str2[*len*80+j+i*80]=usrlist[i][j];
        str = str2;
        *len2 = *len + usrlen;
        len = len2;
    }
    char abbr[81], deft[81], name[81], value[81], value2[81];
    cmdct=0;
    nct=0;
    for (i=0; i<*len; i++){
        if (str[i*80]=='c') cmdct++;
        if (str[i*80]=='n') nct++;
        if (str[i*80]=='r') nopt++;
        c2fortran(str+i*80,80);
        removespaces(str+i*80,80);
    }
    cmdn = (char**)malloc(cmdct*sizeof(char*));
    cmda = (char**)malloc(cmdct*sizeof(char*));
    cmdt = (char**)malloc(cmdct*sizeof(char*));
    cmdpct = (int*)malloc(cmdct*sizeof(int));
    cmdp = (int**)malloc(cmdct*sizeof(int*));
    cmdc = (int*)malloc(cmdct*sizeof(int));
    for (i=0; i<cmdct; i++){
        cmdn[i] = (char*)malloc(maxnamelen+1);
        cmda[i] = (char*)malloc(maxabbrlen+1);
        cmdt[i] = (char*)malloc(maxnamelen+1);
        cmdp[i] = (int*)malloc(nct*sizeof(int));
        cmdc[i] = -1;
        for (j=0; j<nct; j++) cmdp[i][j]=-1;
    }
    nn = (char**)malloc(nct*sizeof(char*));
    na = (char**)malloc(nct*sizeof(char*));
    nd = (char**)malloc(nct*sizeof(char*));
    no = (int*)malloc(nct*sizeof(int));
    nu = (int*)malloc(nct*sizeof(int));
    nw = (int*)malloc(nct*sizeof(int));
    ni = (int*)malloc(nct*sizeof(int));
    nt = (char*)malloc(nct);
    for (i=0; i<nct; i++){
        nn[i] = (char*)malloc(maxnamelen+1);
        na[i] = (char*)malloc(maxabbrlen+1);
        nd[i] = (char*)malloc(maxdeftlen+1);
    }
    webpageA = (char*)malloc(maxwebpage);
    webpageB = (char*)malloc(maxwebpage);
    
    nct=0;
    for (i=0; i<*len; i++)
    //record variable names, abbreviations, and default values
    if (str[i*80]=='n'){
        parse(str+i*80+1,"n",name);
        parse(str+i*80+1,"a",abbr);
        parse(str+i*80+1,"d",deft);
        parse(str+i*80+1,"t",value);
        parse(str+i*80+1,"i",value2);
        name[maxnamelen]='\0';
        abbr[maxabbrlen]='\0';
        deft[maxnamelen]='\0';
        value2[maxnamelen]='\0';
        removeapost(name);
        removeapost(abbr);
        removeapost(deft);
        if (name[0]!='\0'){
            if (value[0]=='\0') {
                printf("webgui: WARNING: parameter %s should declare type, calls to webupdate will fail\n",name);
                value[0]='?';
            }
            if (value[0]=='i' && isint(deft)==0){
                printf("webgui: WARNING: parameter %s has default value of type not int, defaulting to 0\n",name);
                strcpy(deft,"0");
            }
            else if (value[0]=='r' && isreal(deft)==0){
                printf("webgui: WARNING: parameter %s has default value of type not real, defaulting to 0\n",name);
                strcpy(deft,"0");
            }
            strcpy(nn[nct],name);
            strcpy(na[nct],abbr);
            remove0e(deft);
            strcpy(nd[nct],deft);
            if (i<*len-usrlen)
            if (value[0]!='?' && (value2[0]=='\0' || isint(value2)==0 || isvalid(str2int(value2),value[0])==0)) {
                strcpy(value2,"0");
                printf("webgui: WARNING: parameter %s has an invalid index, calls to webupdate will fail\n",name);
            }
            ni[nct] = str2int(value2)-1;
            no[nct]=0;
            if (i<*len-usrlen) nu[nct]=0;
            else nu[nct]=1;
            nw[nct]=0;
            nt[nct] = value[0];
            nct++;
        }
    }
    count=0;
    for (i=0; i<*len; i++)
    //mark which variables have a descriptive options list
    if (str[i*80]=='s'){
        parse(str+i*80+1,"n",name);
        removeapost(name);
        int n = getindexbyname(name);
        if (n>=0) {
            no[n]=1;
            count++;
        }
        else printf("webgui: WARNING: parameter %s needs to be declared, ignoring associated options\n",name);
    }
    cmdct=0;
    for (i=0; i< *len; i++)
    //record command names and abbreviations.
    if (str[i*80]=='c'){
        parse(str+i*80+1,"c",name);
        parse(str+i*80+1,"k",abbr);
        parse(str+i*80+1,"t",value);
        name[maxnamelen]='\0';
        abbr[maxabbrlen]='\0';
        value[maxnamelen]='\0';
        removeapost(name);
        removeapost(abbr);
        removeapost(value);
        if (name[0]!='\0'){
            strcpy(cmdn[cmdct],name);
            if (abbr[0]=='\0'){
                strncpy(abbr,name,3);
                abbr[3]='\0';
                for (k=0;k<3;k++) abbr[k] = tolower(abbr[k]);
                printf("webgui: WARNING: command %s needs an abbreviation, defaulting to %s\n",name,abbr);
            }
            strcpy(cmda[cmdct],abbr);
            strcpy(cmdt[cmdct],value);
            cmdct++;
        }
    }
    for (k=0; k<cmdct; k++){
        //record command parameters associations.
        count=0;
        int index;
        for (i=0; i< *len; i++)
        if (str[i*80]=='r'){
            parse(str+i*80+1,"c",value);
            removeapost(value);
            if (strcmp(value,cmdn[k])==0){
                parse(str+i*80+1,"n",name);
                removeapost(name);
                getdeftbyname(name,deft,abbr,&nopt,&index);
                if (index>=0){
                    nw[index]=1;
                    if (strlen(deft)==0 && (nt[index]=='i' || nt[index]=='r')){
                        printf("webgui: WARNING: parameter %s should declare a default value, defaulting to 0\n",name);
                        strcpy(nd[index],"0");
                    }
                    cmdp[k][count]=index;
                    count++;
                }
                else printf("webgui: WARNING: parameter %s needs to be declared, ignoring command association\n",name);
            }
        }
        cmdpct[k]=count;
    }
    /* below creates part 2 of 4 for index.html and sg for web browser */
    strcpy(webpageB,"");
    int blen=0;
    for (k=0; k<nct; k++)
    //add parameter descriptive options lists to web page.
    if (no[k]==1){
        blen += sprintf(webpageB+blen,"<div id='%soptions' style='display:none'>\n  %s options:<br>\n",nn[k],nn[k]);
        for (i=0; i<*len; i++)
        if (str[i*80]=='s'){
            parse(str+i*80+1,"n",abbr);
            removeapost(abbr);
            if (strcmp(abbr,nn[k])==0){
                parse(str+i*80+1,"l",name);
                parse(str+i*80+1,"v",value);
                removeapost(value);
                blen += sprintf(webpageB+blen,"  <input type='radio' name='%sradio' value='%s' onclick='setValue(this)'> %s<br>\n",nn[k],value,name);
            }
        }
        blen += sprintf(webpageB+blen,"  <br>\n</div>\n\n");
    }
    blen += sprintf(webpageB+blen,"<!-- File selection menu -->\n");
    blen += sprintf(webpageB+blen,"<div id='text2' style='display:none'>\n");
    blen += sprintf(webpageB+blen,"<iframe id='text3' width=600 height=300></iframe>\n</div>\n\n");
    blen += sprintf(webpageB+blen,"</div><!-- id='box' -->\n\n");
    blen += sprintf(webpageB+blen,"<!-- Command line submission -->\n<div id='head2' style='display:none'>\n");
    char *temp = webpageB;
    webpageB = realloc(webpageB,strlen(webpageB)+1);
    if (webpageB==NULL) webpageB = temp;
    if (strlen(webpageB)>maxwebpage) printf("webgui: ERROR: increase maxwebpage (because of webpageB)\n");
    if (init0==1) free(str);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int webstart_(int *x){
    /* Call this to start the service */
    /* where x is the desired port to listen on. */
    /* After calling this, any web browser can connect to the */
    /* server with the URL = http://ADDRESS:PORT */
    /* returns -1 if port is already in use */
    /* returns -2 if error creating socket */
    
    int i;
    if (running==1) return 0;
    running=1;
    if (query==-1) {query = 0; query2 = 0;}
    else {query = 1; query2 = 1;}
    history = (char**)malloc(maxhistory*sizeof(char*));
    for (i=0; i<maxhistory; i++) {
        history[i] = (char*)malloc(90);
        history[i][0]='\0';
    }
    hindex = 0;
    webpageD = (char*)malloc(110*maxhistory+100);
    webpageD[0] = 0;
    bufferA = (char*)malloc(80*maxlines);
    bufferB = (char*)malloc(80*maxlines);
    if (load_webpageC_from_file==1){
        char buffer[1024];
        if (access("indexC.html",F_OK)==0){
            webpageC = (char*)malloc((int)fsize("indexC.html")+1);
            webpageC[0] = '\0';
            FILE *fp;
            fp = fopen("indexC.html","r");
            while (fgets(buffer, 255, fp)) strcat(webpageC,buffer);
            fclose(fp);
        }
        else{
            printf("webgui: WARNING: server can't find indexC.html, defaulting to internal indexC.html\n");
            updatewebpageC();
        }
    }
    else updatewebpageC();
    if (webpageA==NULL){
        webpageA = (char*)malloc(1000);
        updatewebpageA(-1);
        strcat(webpageA,"\n\n<!-- Command line submission -->\n<div id='head2' style='display:inline-block'>\n");
    }
    int nx = 4;
    int ny = 1;
    int img[4] = {0,0,0,0};
    double color = 1.0;
    for (i=3; i<6; i++){
        websetcolors_(&ny,&color,&color,&color,&i);
        webimagedisplay_(&nx,&ny,img,&i);
    }
    if ((create_socket = socket(AF_INET, SOCK_STREAM, 0)) < 0){
        printf("webgui: ERROR: server can't create socket %d (%s)\n",*x,strerror(errno));
        running = 0;
        return -2;
    }
    int yes=1;
    if (setsockopt(create_socket, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(int))<0){
        printf("webgui: ERROR: server can't set socket %d (%s)\n",*x,strerror(errno));
        running = 0;
        return -2;
    }
    address.sin_family = AF_INET;
    address.sin_addr.s_addr = INADDR_ANY;
    address.sin_port = htons(*x);
    
    if (bind(create_socket, (struct sockaddr *) &address, sizeof(address)) == 0)
        printf("webgui: Listening on port %d for web browser...\n",*x);
    else {
        printf("webgui: FAILURE: server can't bind port %d (%s)\n",*x,strerror(errno));
        running = 0;
        return -1;
    }
    memset(bufferA,' ',80*maxlines);
    memset(bufferB,' ',80*maxlines);
    pthread_create(&pth,NULL,startlisten,NULL);
    gettimeofday(&started, NULL);
    webwritenline("#start,",1);
    return 0;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webstop_(){
    /* call this to stop the service */
    /* this terminates thread running web server and frees memory */
    
    if (running==0) return;
    while (indexB>0) usleep(1000);
    stopthread = 1;
    int i;
    char str[4];
    for (i=0;i<6;i++){
        sprintf(str,"x=%d",i);
        releaseWebGL(str);
    }
    free(webpageC);
    free(webpageD);
    running = 0;
    initialized = 0;
    init0 = 0;
    waiting = 0;
    bufferwaitA = 0;
    bufferwaitB = 0;
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webreadline_(char *str){
    /* Call this to receive one command string from the web browser */
    /* where str is char[80] i.e. can hold 80 characters */
    /* NOTE this call will not return until there is a string to return */
    /* If the command string buffer is empty, it will wait */
    
    int i;
    if (running==0) return;
    while (indexA<80 || bufferwaitA==1) usleep(1000);
    bufferwaitA=1;
    for (i=0;i<80;i++) str[i]=bufferA[i];
    for (i=0;i<80*maxlines-80;i++) bufferA[i]=bufferA[i+80];
    for (i=80*maxlines-80;i<80*maxlines;i++) bufferA[i]=' ';
    indexA-=80;
    bufferwaitA=0;
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webwriteline_(char *str){
    /* Call this to display one output string to the web browser */
    /* where str is char[80] or less as either space terminated or null terminated string */
    /* ignores blank line writes, removes carriage returns, and removes number signs # */
    
    int i;
    if (running==0) return;
    while (bufferwaitB==1) usleep(1000);
    while (indexB>=80*maxlines) {
        usleep(1000);
        shrinkBuffer();
    }
    bufferwaitB=1;
    int blank=1;
    for (i=0;i<80;i++)
    if (str[i]!=' ' && str[i]!='\n' && str[i]!='\r') blank=0;
    if (blank==1 || str[0]=='\0') return;
    for (i=0;i<80;i++) {
        if (str[i]=='\0') blank=1;
        if (blank==0 && str[i]!='\n' && str[i]!='\r' && str[i]!='#') bufferB[i+indexB]=str[i];
        else bufferB[i+indexB]=' ';
    }
    indexB+=80;
    bufferwaitB=0;
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void shrinkBuffer(){
    while (bufferwaitB==1) usleep(1000);
    bufferwaitB=1;
    int i, step;
    step = 80 + 80 * countskips(4);
    if (bufferB[0]!='#'){
        strncpy(history[hindex],bufferB,80);
        char *index = history[hindex]+79;
        while (*index==' ') {
           *index='\0';
           index--;
        }
        if (history[hindex][0]=='\0') history[hindex][0]=' ';
        hindex++; if (hindex==maxhistory) hindex=0;
    }
    for (i=0;i<80*maxlines-step;i++) bufferB[i]=bufferB[i+step];
    for (i=80*maxlines-step;i<80*maxlines;i++) bufferB[i]=' ';
    indexB -= step;
    bufferwaitB=0;
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webwritenline(char *str, int n){
    /* where str is char[80*n] or less as either space terminated or null terminated string */
    /* ignores blank line writes and removes carriage returns */
    /* max n is 25 to prevent buffer overflow in startlisten*/
    
    int i;
    if (n>25) n=25;
    else if (n<1) n=1;
    if (running==0) return;
    while (bufferwaitB==1) usleep(1000);
    while (indexB+80*(n-1)>=80*maxlines){
        usleep(1000);
        shrinkBuffer();
    }
    bufferwaitB=1;
    int blank=1;
    for (i=0;i<80*n;i++)
        if (str[i]!=' ' && str[i]!='\n' && str[i]!='\r') blank=0;
    if (blank==1 || str[0]=='\0') return;
    int s = 2;
    if (n>1){
        sprintf(bufferB+indexB,"#%d",n);
        if (n>=10) s=3;
    }
    else s = 0;
    for (i=0;i<80*n-s;i++) {
        if (str[i]=='\0') blank=1;
        if (blank==0) bufferB[i+indexB+s]=str[i];
        else bufferB[i+indexB+s]=' ';
    }
    indexB+=80*n;
    bufferwaitB=0;
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webupdate_(int *ip, double *rp, char *sp){
    /* call this to update parameter values */
    
    if (initialized==0) {
        printf("webgui: WARNING: webupdate called before webinit, ignoring call\n");
        return;
    }
    char str[80], str2[2048];
    strcpy(str2,"#update,");
    int i;
    for (i=0;i<nct;i++) if (nu[i]==0 && ni[i]>=0 && nt[i]!='?'){
        strcpy(str,"");
        if (nt[i]=='i') sprintf(str,"%d",ip[ni[i]]);
        else if (nt[i]=='r') sprintf(str,"%g",rp[ni[i]]);
        else strncpy(str,sp+80*ni[i],80);
        fortran2c(str,79,0);
        if (strcmp(nd[i],str)!=0 && nw[i]==1){
            strcpy(nd[i],str);
            if (nt[i]!='i' && nt[i]!='r') fortran2c(str,79,1);
            sprintf(str2+strlen(str2),"%s=%s,",nn[i],str);
        }
    }
    int n = 1+(int)strlen(str2)/80;
    if (running==1 && strlen(str2)>8) webwritenline(str2,n);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webupdate2_(int *ip, double *rp, char *sp, int *iu, double *ru, char *su){
    /* call this to update parameter values and PLTMG usr parameter values */
    
    if (initialized==0) {
        printf("webgui: WARNING: webupdate2 called before webinit, ignoring call\n");
        return;
    }
    char str[80], str2[2048];
    strcpy(str2,"#update,");
    int i;
    for (i=0;i<nct;i++) if (ni[i]>=0 && nt[i]!='?'){
        strcpy(str,"");
        if (nu[i]==1){
            if (nt[i]=='i') sprintf(str,"%d",iu[ni[i]]);
            else if (nt[i]=='r') sprintf(str,"%g",ru[ni[i]]);
            else strncpy(str,su+80*ni[i],80);
        }
        else{
            if (nt[i]=='i') sprintf(str,"%d",ip[ni[i]]);
            else if (nt[i]=='r') sprintf(str,"%g",rp[ni[i]]);
            else strncpy(str,sp+80*ni[i],80);
        }
        fortran2c(str,79,0);
        if (strcmp(nd[i],str)!=0 && nw[i]==1){
            strcpy(nd[i],str);
            if (nt[i]!='i' && nt[i]!='r') fortran2c(str,79,1);
            sprintf(str2+strlen(str2),"%s=%s,",nn[i],str);
        }
    }
    int n = 1+(int)strlen(str2)/80;
    if (running==1 && strlen(str2)>8) webwritenline(str2,n);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int webquery_(){
    /* returns 1 if web browser buttons are showing */
    /* returns 0 if web browser command line is showing */
    /* returns 2 if web server is initiated but not started */
    /* returns -1 if web server is neither init nor started */
    
    return query;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void websetmode_(int *x){
    /* x=4,5,6 sets web browser display frame rate to 10,20,30 fps, */
    /* and sends key and mouse presses via following command strings */
    /* "key code=XXX" */
    /* "mse button=AAA,x=BBB,y=CCC,pane=DDD" */
    /* x=1,2,3 has 2 fps and sends key only, mouse only, key+mouse */
    /* x=7,8,9 sets web browser display frame rate to 10,20,30 fps only*/
    /* x=0 is default, 2 fps and sends no key or mouse */
    /* x=-1 is x=0 but WebGL objects don't reset position on new object */
    /* x=-2,-3,-4 is x=1,2,3 but WebGL objects reset on new object */
    
    if (*x<-4 || *x>9) {
        printf("webgui: WARNING: invalid x in websetmode call, ignoring call\n");
        return;
    }
    int codes[10]={0,5,6,4,1,2,3,7,8,9};
    if (*x<0) animate = *x;
    else animate = codes[*x];
    char str[20];
    sprintf(str,"#animate,%d,",animate);
    if (running==1) webwritenline(str,1);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void allupdate(){
    /* the webbrowser calls this to request most recent variables */
    
    if (initialized==0) return;
    char str2[2048];
    strcpy(str2,"#update,");
    int i;
    for (i=0;i<nct;i++)
        if (nw[i]==1) {
            if (nt[i]=='i' || nt[i]=='r') sprintf(str2+strlen(str2),"%s=%s,",nn[i],nd[i]);
            else sprintf(str2+strlen(str2),"%s=\"%s\",",nn[i],nd[i]);
        }
    int n = 1+(int)strlen(str2)/80;
    if (running==1 && strlen(str2)>8) webwritenline(str2,n);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webupdate3_(int *iu, double *ru, char *su){
    /* call this to update only PLTMG usr parameter values */
    
    if (initialized==0) {
        printf("webgui: WARNING: webupdate3 called before webinit, ignoring call\n");
        return;
    }
    char str[80], str2[2048];
    strcpy(str2,"#update,");
    int i;
    for (i=0;i<nct;i++) if (nu[i]==1 && ni[i]>=0 && nt[i]!='?'){
        strcpy(str,"");
        if (nt[i]=='i') sprintf(str,"%d",iu[ni[i]]);
        else if (nt[i]=='r') sprintf(str,"%g",ru[ni[i]]);
        else strncpy(str,su+80*ni[i],80);
        fortran2c(str,79,0);
        if (strcmp(nd[i],str)!=0 && nw[i]==1){
            strcpy(nd[i],str);
            if (nt[i]!='i' && nt[i]!='r') fortran2c(str,79,1);
            sprintf(str2+strlen(str2),"%s=%s,",nn[i],str);
        }
    }
    int n = 1+(int)strlen(str2)/80;
    if (running==1 && strlen(str2)>8) webwritenline(str2,n);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void websettitle_(char *str, int len){
    if (len>80) len=80;
    strncpy(title,str,len);
    title[len]=0;
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void websetcolors_(int* nc, double* red, double* green, double* blue, int* ipane){
    /* call this before calling webimagedisplay, webframe, webfill, webline, or webgl */
    /* nc is number of colors. red, green, blue are 0<=x<=1 */
    /* ipane is which pane to display in the web browser. Panes 0,1,2 are for */
    /* images and Panes 3,4,5 are for WebGL display */
    
    if (running==0 || *ipane<0 || *ipane>5 || *nc<1) {
        if (running==1)
            printf("webgui: WARNING: invalid ipane in call websetcolors, ignoring call\n");
        return;
    }
    int i;
    while (lock[*ipane]==1) usleep(100);
    lock2[*ipane]=1;
    if (*ipane>2){
        if (colors[*ipane-3]!=NULL) {
            for (i=0;i<ncolor[*ipane-3];i++) free(colors[*ipane-3][i]);
            free(colors[*ipane-3]);
            colors[*ipane-3]=NULL;
        }
        colors[*ipane-3] = (unsigned char**)malloc(*nc * sizeof(unsigned char*));
        if (colors[*ipane-3]==NULL) printf("webgui: ERROR: malloc failed to init colors\n");
        for (i=0;i<*nc;i++) colors[*ipane-3][i] = malloc(3 * sizeof(unsigned char));
        for (i=0;i<*nc;i++){
            colors[*ipane-3][i][0] = (unsigned char)(red[i]*255);
            colors[*ipane-3][i][1] = (unsigned char)(green[i]*255);
            colors[*ipane-3][i][2] = (unsigned char)(blue[i]*255);
        }
        ncolor[*ipane-3] = *nc;
        if (*nc>256) {
            printf("webgui: WARNING: only 256 colors are allowed for 2D images, ignoring extras\n");
            ncolor[*ipane-3]=256;
        }
    }
    else{
        int black = 0;
        /* we set colors for WebGL. Initialize data structures */
        if (colorsGL[*ipane]!=NULL) {
            for (i=0;i<ncolorGL[*ipane];i++) free(colorsGL[*ipane][i]);
            free(colorsGL[*ipane]);
            colorsGL[*ipane]=NULL;
        }
        colorsGL[*ipane] = (float**)malloc(*nc * sizeof(float*));
        if (colorsGL[*ipane]==NULL) printf("webgui: ERROR: malloc failed to init colorsGL\n");
        for (i=0;i<*nc;i++) colorsGL[*ipane][i] = malloc(3 * sizeof(float));
        for (i=0;i<*nc;i++){
            colorsGL[*ipane][i][0] = (float)red[i];
            colorsGL[*ipane][i][1] = (float)green[i];
            colorsGL[*ipane][i][2] = (float)blue[i];
            if (red[i]==0 && green[i]==0 && blue[i]==0) black = i+1;
        }
        ncolorGL[*ipane] = *nc;
        cpane = *ipane + 3;
        if (triangles[*ipane]!=NULL) {
            for (i=0;i<11;i++) free(triangles[*ipane][i]);
            free(triangles[*ipane]);
            triangles[*ipane]=NULL;
        }
        maxtri = starttri;
        triangles[*ipane] = (float**)malloc(11 * sizeof(float*));
        if (triangles[*ipane]==NULL) printf("webgui: ERROR: malloc failed to init triangles\n");
        for (i=0;i<11;i++) triangles[*ipane][i] = malloc(maxtri * sizeof(float));
        indexT[*ipane]=0;
        if (lines[*ipane]!=NULL) {
            for (i=0;i<8;i++) free(lines[*ipane][i]);
            free(lines[*ipane]);
            lines[*ipane]=NULL;
        }
        maxlin = startlin;
        lines[*ipane] = (float**)malloc(8 * sizeof(float*));
        if (lines[*ipane]==NULL) printf("webgui: ERROR: malloc failed to init lines\n");
        for (i=0;i<8;i++) lines[*ipane][i] = malloc(maxlin * sizeof(float));
        indexL[*ipane]=0;
        for (i=0;i<10;i++) tricount[*ipane][i]=0;
        for (i=0;i<10;i++) ccount[*ipane][i]=black;
    }
    lock2[*ipane]=0;
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webimagedisplay_(int* nx, int* ny, int* image, int* ipanex){
    /* Call this to display an image in the web browser, ipane is 0,1,2. */
    /* Call websetcolors before this. image's values refer to colors */
    /* NOTE: nx must be a multiple of 4 */
    
    if (running==0 || *ipanex<3 || *ipanex>5 || ncolor[*ipanex-3]==0) {
        if (running==1 && (*ipanex<3 || *ipanex>5))
            printf("webgui: WARNING: invalid ipane in call webimagedisplay, ignoring call\n");
        return;
    }
    if (*nx%4!=0) {
        printf("webgui: WARNING: nx must be divisible by 4 in call webimagedisplay, ignoring call\n");
        return;
    }
    int i, j, ipanexx=0, *ipane=&ipanexx;
    for (i=0;i<*nx*(*ny);i++) if ( (unsigned char)image[i]>ncolor[*ipanex-3]-1){
        printf("webgui: WARNING: invalid color(s) in image in call webimagedisplay (c=%d, mx=%d)\n",(unsigned char)image[i],ncolor[*ipanex-3]-1);
        i = *nx*(*ny);
    }
    *ipane = *ipanex - 3;
    char str[20];
    while (lock[*ipanex]==1) usleep(100);
    lock2[*ipanex]=1;
    if (bitmap[*ipane]!=NULL) {free(bitmap[*ipane]); bitmap[*ipane]=NULL;}
    bitmaplen[*ipane] = 14+40+4*ncolor[*ipane]+*nx*(*ny);
    bitmap[*ipane] = (unsigned char*)malloc(bitmaplen[*ipane]);
    bitmap[*ipane][0]='B'; //bitmap ID field
    bitmap[*ipane][1]='M'; //bitmap ID field
    *(int*)(bitmap[*ipane]+2) = bitmaplen[*ipane]; //bitmap size
    *(int*)(bitmap[*ipane]+6) = 0; //application info
    *(int*)(bitmap[*ipane]+10) = 14+40+4*ncolor[*ipane]; //offset of pixel data
    *(int*)(bitmap[*ipane]+14) = 40; //size of dib header
    *(int*)(bitmap[*ipane]+18) = *nx; //width of bitmap
    *(int*)(bitmap[*ipane]+22) = *ny; //height of bitmap
    *(short*)(bitmap[*ipane]+26) = 1; //number of color planes
    *(short*)(bitmap[*ipane]+28) = 8; //bits per pixel
    *(int*)(bitmap[*ipane]+30) = 0; //compression
    *(int*)(bitmap[*ipane]+34) = *nx*(*ny); //size of pixel data including padding
    *(int*)(bitmap[*ipane]+38) = 2835; //72dpi print res width
    *(int*)(bitmap[*ipane]+42) = 2835; //72dpi print res height
    *(int*)(bitmap[*ipane]+46) = ncolor[*ipane]; //number of colors
    *(int*)(bitmap[*ipane]+50) = 0; //number of important colors
    for (i=0;i<ncolor[*ipane];i++){
        bitmap[*ipane][54+i*4] = colors[*ipane][i][2];
        bitmap[*ipane][55+i*4] = colors[*ipane][i][1]; //colors
        bitmap[*ipane][56+i*4] = colors[*ipane][i][0];
        bitmap[*ipane][57+i*4] = 0;
    }
    for (j=0;j<*ny;j++)
    for (i=0;i<*nx;i++)
    bitmap[*ipane][54+ncolor[*ipane]*4+i+j*(*nx)] = (unsigned char)image[i+j*(*nx)];
    lock2[*ipanex]=0;
    sprintf(str,"#image,600,400,%d,",*ipane);
    if (!(*nx==4 && *ny==1)) {
        webwritenline(str,1);
        sg[*ipane] = -1;
        pic[*ipane] = 1;
        if ((animate>=1 && animate<=3) || (animate>=7 && animate<=9)){
            lock[*ipanex]=1; while (lock[*ipanex]==1) usleep(100);
        }
        else usleep(500);
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webframe_(int* iframe){
    /* Call this before calling webfill or webline              */
    /* This determines where the polygon or line will draw      */
    /* All calls to webfill and webline after this will go to   */
    /* the respective frame. If you never call, default is 1    */
    /*                                                          */
    /*                                                          */
    /*       frame/list equivalence table                       */
    /*        ___ ___ ___       ___ ___ ___                     */
    /*       |       |   |     |           |                    */
    /*       |       | 2 |     |           |                    */
    /*       |   4   |___|     |     1     |                    */
    /*       |       |   |     |           |                    */
    /*       |       | 3 |     |           |                    */
    /*       |___ ___|___|     |___ ___ ___|                    */
    /*                                                          */
    /*        list    frame        type                         */
    /*                                                          */
    /*          1       1          non-rotating, non-lighted    */
    /*                                                          */
    /*          2       2          non-rotating, non-lighted    */
    /*                                                          */
    /*          3       3          non-rotating, non-lighted    */
    /*                                                          */
    /*          4       4          non-rotating, non-lighted    */
    /*          5       4              rotating, non-lighted    */
    
    if (running==0 || cpane<3 || cpane>5) {
        if (running==1)
            printf("webgui: WARNING: webframe called before websetcolors, ignoring call\n");
        return;
    }
    cframe = *iframe;
    if (cframe<1 || cframe>5) {
        if (cframe<-5 || cframe>5 || cframe==0)
            printf("webgui: WARNING: invalid iframe in call webframe, defaulting to 1\n");
        cframe = 1;
    }
    return;
}
/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webfillflt_(float* x, float* y, float* z, int* n, int* icolor){
    /* call websetcolors and webframe before this. */
    /* Calling this will place one convex polygon in a buffer which will */
    /* get drawn in the requested frame after you call webgl_            */
    /* n is the number of vertices and x,y,z are the coordinates in 3-D */
    /* icolor is the color of the triangle and references colors from websetcolors */
    /* 0<=x,y,z<=1 and the polygon will be located in the respective frame */
    /* For frame 1, 0<=x<=1.5 instead of 0<=x<=1 */
    /* You choose which pane to draw into with your call to websetcolors */
    
    if (running==0 || cpane<3 || cpane>5 || cframe<0 || *n<3) {
        if (running==1 && *n>=3)
            printf("webgui: WARNING: webfill called before websetcolors, ignoring call\n");
        return;
    }
    while (lock[cpane-3]==1) usleep(100);
    lock2[cpane-3]=1;
    if (indexT[cpane-3]>=maxtri+3-(*n)) if (growtri(cpane-3,0)>0) return;
    int i, color = *icolor;
    if (*icolor<1 || *icolor>ncolorGL[cpane-3]){
        printf("webgui: WARNING: invalid icolor in call webfill, defaulting to 1\n");
        color = 1;
    }
    for (i=0;i<*n-2;i++){
        triangles[cpane-3][0][indexT[cpane-3]]=x[0];
        triangles[cpane-3][1][indexT[cpane-3]]=y[0];
        triangles[cpane-3][2][indexT[cpane-3]]=z[0];
        triangles[cpane-3][3][indexT[cpane-3]]=x[i+1];
        triangles[cpane-3][4][indexT[cpane-3]]=y[i+1];
        triangles[cpane-3][5][indexT[cpane-3]]=z[i+1];
        triangles[cpane-3][6][indexT[cpane-3]]=x[i+2];
        triangles[cpane-3][7][indexT[cpane-3]]=y[i+2];
        triangles[cpane-3][8][indexT[cpane-3]]=z[i+2];
        triangles[cpane-3][9][indexT[cpane-3]]=color;
        triangles[cpane-3][10][indexT[cpane-3]]=cframe;
        indexT[cpane-3]++;
        tricount[cpane-3][cframe-1]++;
        if (ccount[cpane-3][cframe-1]!=color) ccount[cpane-3][cframe-1]=-1;
    }
    lock2[cpane-3]=0;
    return;
}
/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webfilldbl_(double* x, double* y, double* z, int* n, int* icolor){
    /* same as above but takes double precision */
    
    if (running==0 || cpane<3 || cpane>5 || cframe<0 || *n<3){
        if (running==1 && *n>=3)
            printf("webgui: WARNING: webfill called before websetcolors, ignoring call\n");
        return;
    }
    while (lock[cpane-3]==1) usleep(100);
    lock2[cpane-3]=1;
    if (indexT[cpane-3]>=maxtri+3-(*n)) if (growtri(cpane-3,0)>0) return;
    int i, color = *icolor;
    if (*icolor<1 || *icolor>ncolorGL[cpane-3]){
        printf("webgui: WARNING: invalid icolor in call webfill, defaulting to 1\n");
        color = 1;
    }
    for (i=0;i<*n-2;i++){
        triangles[cpane-3][0][indexT[cpane-3]]=(float)x[0];
        triangles[cpane-3][1][indexT[cpane-3]]=(float)y[0];
        triangles[cpane-3][2][indexT[cpane-3]]=(float)z[0];
        triangles[cpane-3][3][indexT[cpane-3]]=(float)x[i+1];
        triangles[cpane-3][4][indexT[cpane-3]]=(float)y[i+1];
        triangles[cpane-3][5][indexT[cpane-3]]=(float)z[i+1];
        triangles[cpane-3][6][indexT[cpane-3]]=(float)x[i+2];
        triangles[cpane-3][7][indexT[cpane-3]]=(float)y[i+2];
        triangles[cpane-3][8][indexT[cpane-3]]=(float)z[i+2];
        triangles[cpane-3][9][indexT[cpane-3]]=color;
        triangles[cpane-3][10][indexT[cpane-3]]=cframe;
        indexT[cpane-3]++;
        tricount[cpane-3][cframe-1]++;
        if (ccount[cpane-3][cframe-1]!=color) ccount[cpane-3][cframe-1]=-1;
    }
    lock2[cpane-3]=0;
    return;
}
/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void weblineflt_(float* x, float* y, float* z, int* n, int* icolor){
    /* call websetcolors and webframe before this. */
    /* Calling this will place one line in a buffer which will */
    /* get drawn in the requested frame after you call webgl_            */
    /* n is the number of vertices and x,y,z are the coordinates in 3-D */
    /* icolor is the color of the line and references colors from websetcolors */
    /* 0<=x,y,z<=1 and the line will be located in the respective frame */
    /* For frame 1, 0<=x<=1.5 instead of 0<=x<=1 */
    /* You choose which pane to draw in your call to websetcolors */
    
    if (running==0 || cpane<3 || cpane>5 || cframe<0 || *n<2){
        if (running==1 && *n>=2)
            printf("webgui: WARNING: webline called before websetcolors, ignoring call\n");
        return;
    }
    while (lock[cpane-3]==1) usleep(100);
    lock2[cpane-3]=1;
    if (indexL[cpane-3]>=maxlin+2-(*n)) if (growlin(cpane-3,0)>0) return;
    int i, color = *icolor;
    if (*icolor<1 || *icolor>ncolorGL[cpane-3]){
        printf("webgui: WARNING: invalid icolor in call webline, defaulting to 1\n");
        color = 1;
    }
    for (i=0;i<*n-1;i++){
        lines[cpane-3][0][indexL[cpane-3]]=x[i];
        lines[cpane-3][1][indexL[cpane-3]]=y[i];
        lines[cpane-3][2][indexL[cpane-3]]=z[i];
        lines[cpane-3][3][indexL[cpane-3]]=x[i+1];
        lines[cpane-3][4][indexL[cpane-3]]=y[i+1];
        lines[cpane-3][5][indexL[cpane-3]]=z[i+1];
        lines[cpane-3][6][indexL[cpane-3]]=color;
        lines[cpane-3][7][indexL[cpane-3]]=cframe;
        indexL[cpane-3]++;
        tricount[cpane-3][cframe+4]++;
        if (ccount[cpane-3][cframe+4]!=color) ccount[cpane-3][cframe+4]=-1;
    }
    lock2[cpane-3]=0;
    return;
}
/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void weblinedbl_(double* x, double* y, double* z, int* n, int* icolor){
    /* same as above but takes double precision */
    
    if (running==0 || cpane<3 || cpane>5 || cframe<0 || *n<2){
        if (running==1 && *n>=2)
            printf("webgui: WARNING: webline called before websetcolors, ignoring call\n");
        return;
    }
    while (lock[cpane-3]==1) usleep(100);
    lock2[cpane-3]=1;
    if (indexL[cpane-3]>=maxlin+2-(*n)) if (growlin(cpane-3,0)>0) return;
    int i, color = *icolor;
    if (*icolor<1 || *icolor>ncolorGL[cpane-3]){
        printf("webgui: WARNING: invalid icolor in call webline, defaulting to 1\n");
        color = 1;
    }
    for (i=0;i<*n-1;i++){
        lines[cpane-3][0][indexL[cpane-3]]=(float)x[i];
        lines[cpane-3][1][indexL[cpane-3]]=(float)y[i];
        lines[cpane-3][2][indexL[cpane-3]]=(float)z[i];
        lines[cpane-3][3][indexL[cpane-3]]=(float)x[i+1];
        lines[cpane-3][4][indexL[cpane-3]]=(float)y[i+1];
        lines[cpane-3][5][indexL[cpane-3]]=(float)z[i+1];
        lines[cpane-3][6][indexL[cpane-3]]=color;
        lines[cpane-3][7][indexL[cpane-3]]=cframe;
        indexL[cpane-3]++;
        tricount[cpane-3][cframe+4]++;
        if (ccount[cpane-3][cframe+4]!=color) ccount[cpane-3][cframe+4]=-1;
    }
    lock2[cpane-3]=0;
    return;
}
/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webgldisplay_(int* ipane){
    /* call websetcolors, webframe, webfill, and webline before this. */
    /* This will draw all the objects for ipane in the buffer to the web browser */

    /* currently creates preamble for data0.gpu, but most of this code */
    /* can be moved to inside the function updatedatabuffer3 */
    if (running==0 || *ipane<0 || *ipane>2) {
        if (running==1)
            printf("webgui: WARNING: invalid ipane in webgldisplay call, ignoring call\n");
        return;
    }
    char str[80*5];
    int i, frames[5]={5,3,2,4,1};
    strcpy(str,"#webgl2,");
    for (i=0;i<5;i++) {
        dbpreamble[*ipane][2*i]=tricount[*ipane][frames[i]-1];
        dbpreamble[*ipane][2*i+1]=tricount[*ipane][frames[i]+4];
    }
    for (i=0;i<5;i++) {
        dbpreamble[*ipane][2*i+10]=tricount[*ipane][frames[i]-1];
        if (ccount[*ipane][frames[i]+4]>0) dbpreamble[*ipane][2*i+11]=0;
        else dbpreamble[*ipane][2*i+11]=tricount[*ipane][frames[i]+4];
    }
    sprintf(str+strlen(str),"%d,",*ipane);
    int n = 1+(int)strlen(str)/80;
    webwritenline(str,n);
    sg[*ipane] = 1;
    pic[*ipane] = -1;
    while (lock[*ipane]==1) usleep(100);
    lock2[*ipane]=1;
    if (maxtri>indexT[*ipane] && indexT[*ipane]!=0) growtri(*ipane,1);
    if (maxlin>indexL[*ipane] && indexL[*ipane]!=0) growlin(*ipane,1);
    lock2[*ipane]=0;
    if ((animate>=1 && animate<=3) || (animate>=7 && animate<=9)){
        lock[*ipane]=1; while (lock[*ipane]==1) usleep(100);
    }
    else usleep(500);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webbutton_(int *highlight, char *cmd, int cmdlen){
    /* call this to highlight a button. Set highlight = 1 or -1 for */
    /* highlighted and unhighlighted respectively.  */
    /* cmd is the button you wish to highlight (give full name)*/
    
    if (initialized==0) return;
    int idx, hlight = *highlight;
    if (hlight!=-1 && hlight!=1){
        printf("webgui: WARNING: invalid highlight in webbutton call, defaulting to -1\n");
        hlight=-1;
    }
    char str[80];
    strncpy(str,cmd,cmdlen);
    str[cmdlen]='\0';
    idx = getindexbycmd(str);
    if (idx!=-1) {
        cmdc[idx] = hlight;
        if (hlight==1) sprintf(str,"#button,%s,lightgrey,",cmda[idx]);
        else sprintf(str,"#button,%s,,",cmda[idx]);
        if (running==1) webwritenline(str,1);
    }
    else{
        printf("webgui: WARNING: invalid command in call webbutton, ignoring call\n");
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void webpause_(){
    /* call this to prompt web browser user to click a button to proceed */
    /* This funciton will not return to the calling program until user click */

    if (running==0) return;
    webwritenline("#pause",1);
    waiting=1;
    while (waiting==1) usleep(1000);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void *startlisten(void *arg){
    /*main function which hosts web server and listens for requests */
    
    int new_socket, msize, i, step=0;
    socklen_t addrlen;
    const int bufsize = 2048;
    char buffer[bufsize], str[bufsize];
    unsigned char *ip;
    
    addrlen = (socklen_t)sizeof(address);
    while (1) {
        if (stopthread==1) pthread_exit(NULL);
        if (listen(create_socket, 10) < 0) {
            printf("webgui: ERROR: server listen error (%s)\n",strerror(errno));
        }
        if ((new_socket = accept(create_socket, (struct sockaddr *) &address, &addrlen)) < 0) {
            printf("webgui: ERROR: server accept error (%s)\n",strerror(errno));
        }
        ip = (unsigned char*)&address.sin_addr;
        //printf("webgui: ACCEPTED from %d.%d.%d.%d \n",ip[0],ip[1],ip[2],ip[3]);
        if (firewall[0]!=0){
            if (ip[0]!=firewall[1] || (firewall[2]==1 && ip[1]!=firewall[3])
            || (firewall[4]==1 && ip[2]!=firewall[5]) || (firewall[6]==1 && ip[3]!=firewall[7])  ){
                close(new_socket);
                //printf("webgui: Blocked %d.%d.%d.%d \n",ip[0],ip[1],ip[2],ip[3]);
                continue;
            }
        }
        msize = recv(new_socket, buffer, bufsize, 0);
        buffer[msize]='\0';
        //printf("webgui: [%s]\n",buffer);
        
        if (strncmp(buffer,"GET",3)==0){
            char *index;
            index = strchr(buffer+4,' ');
            index[0] = '\0';
            strcpy(str,buffer+4);
            //printf("webgui: URL = [%s]\n",str);
            if (strncmp(str,"/readline.php?",14)==0){
                int k = 0;
                if (strlen(str)>=17) k = str[16]-'0';
                if (k<0 || k>2) k = 0;
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                send(new_socket, "Connection: close\n",18, 0);
                if (sg[k]!=-1){
                    send(new_socket, "Content-Length: 10\n",19, 0);
                    send(new_socket, "Content-Type: text/plain\n\n", 26, 0);
                    sprintf(str,"#webgl2,%d,",k);
                    send(new_socket, str, strlen(str), 0);
                    sg[k] = -1;
                    pic[k] = -1;
                }
                else if(pic[k]!=-1){
                    send(new_socket, "Content-Length: 17\n",19, 0);
                    send(new_socket, "Content-Type: text/plain\n\n", 26, 0);
                    sprintf(str,"#image,600,400,%d,",k);
                    send(new_socket, str, strlen(str), 0);
                    sg[k] = -1;
                    pic[k] = -1;
                }
            }
            else if (strcmp(str,"/readline.php")==0){
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                send(new_socket, "Connection: close\n",18, 0);
                if (indexB>=80){
                    while (bufferwaitB==1) usleep(100);
                    bufferwaitB=1;
                    sprintf(str,"Content-Length: %d\n",indexB);
                    send(new_socket, str, strlen(str), 0);
                    send(new_socket, "Content-Type: text/plain\n\n", 26, 0);
                    while (indexB>=80){
                        step = 80 + 80 * countskips(4);
                        send(new_socket, bufferB, step, 0);
                        if (bufferB[0]!='#'){
                            strncpy(history[hindex],bufferB,80);
                            index = history[hindex]+79;
                            while (*index==' ') {
                                *index='\0';
                                index--;
                            }
                            if (history[hindex][0]=='\0') history[hindex][0]=' ';
                            hindex++; if (hindex==maxhistory) hindex=0;
                        }
                        for (i=0;i<80*maxlines-step;i++) bufferB[i]=bufferB[i+step];
                        for (i=80*maxlines-step;i<80*maxlines;i++) bufferB[i]=' ';
                        indexB-=step;
                    }
                    bufferwaitB=0;
                }
            }
            else if (strncmp(str,"/writeline.php",14)==0){
                if (strncmp(str+14,"?cmd=",5)==0) urldecode(str,buffer+23);
                else strcpy(str,"''");
                send(new_socket, "HTTP/1.1 200 OK\n\n", 16, 0);
                send(new_socket, "Connection: close\n",18, 0);
                if (indexA<maxlines*80){
                    while (bufferwaitA==1) usleep(100);
                    bufferwaitA=1;
                    str[79]='\0';
                    strcpy(history[hindex],"command:");
                    for (i=0;i<strlen(str)-2;i++) {
                        bufferA[i+indexA]=str[i+1];
                        history[hindex][8+i]=str[i+1];
                    }
                    history[hindex][8+strlen(str)-2]='\0';
                    for (i=strlen(str)-2;i<80;i++) bufferA[i+indexA]=' ';
                    indexA+=80; hindex++;
                    if (strncmp(str+1,"key",3)==0 || strncmp(str+1,"mse",3)==0) {hindex--; history[hindex][0]=0;}
                    if (hindex==maxhistory) hindex=0;
                    if (initialized==1) updatedeft(str);
                    bufferwaitA=0;
                }
            }
            else if (strncmp(str,"/figure",7)==0 && strncmp(str+8,".bmp",4)==0){
                int k = str[7]-'0';
                if (k<0 || k>2) k = 0;
                while (lock2[k+3]==1) usleep(100);
                lock[k+3]=1;
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                sprintf(str,"Content-Length: %d\n",bitmaplen[k]);
                send(new_socket, str, strlen(str), 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: image/bmp\n\n", 25, 0);
                send(new_socket, bitmap[k], bitmaplen[k], 0);
                lock[k+3]=0;
                if (animate<=0 || (animate>=4 && animate<=6)) usleep(500);
            }
            else if (strncmp(str,"/data",5)==0 && strncmp(str+6,".js",3)==0){
                int k = str[5]-'0';
                if (k<0 || k>2) k = 0;
                int xtra=0; if (strlen(str)>9) xtra=1;
                while (lock2[k]==1) usleep(100);
                lock[k] = 1;
                updatedatabuffer(k,xtra);
                lock[k] = 0;
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                sprintf(str,"Content-Length: %d\n",(int)strlen(databuffer));
                send(new_socket, str, strlen(str), 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: application/javascript\n\n", 38, 0);
                send(new_socket, databuffer, strlen(databuffer), 0);
                free(databuffer); databuffer=NULL;
                if (animate<=0 || (animate>=4 && animate<=6)) usleep(500);
            }
            else if (strncmp(str,"/data",5)==0 && strncmp(str+6,".gpu",4)==0){
                int k = str[5]-'0';
                if (k<0 || k>2) k = 0;
                while (lock2[k]==1) usleep(100);
                lock[k] = 1;
                int sz = updatedatabuffer3(k,webGLendian);
                lock[k] = 0;
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                sprintf(str,"Content-Length: %d\n",sz);
                send(new_socket, str, strlen(str), 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: application/octet-stream\n\n", 40, 0);
                send(new_socket, databuffer, sz, 0);
                free(databuffer); databuffer=NULL;
                if (animate<=0 || (animate>=4 && animate<=6)) usleep(500);
            }
            else if (strncmp(str,"/sg",3)==0){
                int k = 0;
                if (strlen(str)>=7) k = str[6]-'0';
                if (k<0 || k>2) k = 0;
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                if (initialized==1) updatewebpageA(1);
                updatewebpageD2(k,0);
                sprintf(str,"Content-Length: %d\n",(int)(strlen(webpageA) + strlen(webpageB) + strlen(webpageC) + strlen(webpageD)));
                send(new_socket, str, strlen(str), 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: text/html; charset=utf-8\n\n", 40, 0);
                send(new_socket, webpageA, strlen(webpageA), 0);
                send(new_socket, webpageB, strlen(webpageB), 0);
                send(new_socket, webpageC, strlen(webpageC), 0);
                send(new_socket, webpageD, strlen(webpageD), 0);
            }
            else if (load_pngs_from_file==1 && ispng(str)==1){
                if (access(str+1,F_OK)==0){
                    int size = fsize(str+1);
                    unsigned char *buffer;
                    buffer = (unsigned char*)malloc(size);
                    FILE *fp;
                    fp = fopen(str+1,"r");
                    for (i=0;i<size;i++) buffer[i] = fgetc(fp);
                    fclose(fp);
                    send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                    sprintf(str,"Content-Length: %d\n",size);
                    send(new_socket, str, strlen(str), 0);
                    send(new_socket, "Connection: close\n",18, 0);
                    send(new_socket, "Content-Type: image/png\n\n", 25, 0);
                    send(new_socket, buffer, size, 0);
                }
                else printf("webgui: WARNING: server can't find file %s\n",str+1);
            }
            else if (strncmp(str,"/folder.png",11)==0){
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                send(new_socket, "Content-Length: 446\n", 20, 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: image/png\n\n", 25, 0);
                send(new_socket, folderpng, 446, 0);
            }
            else if (strncmp(str,"/up.png",7)==0){
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                send(new_socket, "Content-Length: 472\n", 20, 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: image/png\n\n", 25, 0);
                send(new_socket, uppng, 472, 0);
            }
            else if (strncmp(str,"/file.png",9)==0){
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                send(new_socket, "Content-Length: 402\n", 20, 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: image/png\n\n", 25, 0);
                send(new_socket, filepng, 402, 0);
            }
            else if (strncmp(str,"/callfunct.php",14)==0){
                send(new_socket, "HTTP/1.1 200 OK\n\n", 16, 0);
                send(new_socket, "Connection: close\n",18, 0);
                urldecode(str,buffer+19);
                if (strncmp(str,"continue",8)==0) waiting = 0;
                else if (strncmp(str,"listfiles",9)==0) listfiles(str);
                else if (strncmp(str,"release",7)==0) releaseWebGL(str);
                else if (strncmp(str,"updateall",9)==0) allupdate();
                else if (strncmp(str,"push",4)==0) pushcanvas(str);
                else if (strncmp(str,"query",5)==0) setquery(str);
                else if (strncmp(str,"firewall",8)==0) setfirewall(str,ip);
                else if (strncmp(str,"endian",6)==0) setendian(str);
                else if (strncmp(str,"animate",7)==0) setanimate(str);
            }
            else if (strcmp(str,"/")==0 || strncmp(str,"/index",6)==0 || strncmp(str,"/save",5)==0){
                send(new_socket, "HTTP/1.1 200 OK\n", 16, 0);
                int xtra = 0; if (strcmp(str,"/save")==0) xtra = 1;
                int k = -1;
                if (strlen(str)>=9) k = str[8]-'0';
                if (k<0 || k>2) k = -1;
                if (k==-1) updatewebpageD(xtra);
                else updatewebpageD2(k,1);
                if (initialized==1) updatewebpageA(k+1);
                if (xtra==0) query = query2;
                sprintf(str,"Content-Length: %d\n",(int)(strlen(webpageA) + strlen(webpageB) + strlen(webpageC) + strlen(webpageD)));
                send(new_socket, str, strlen(str), 0);
                send(new_socket, "Connection: close\n",18, 0);
                send(new_socket, "Content-Type: text/html; charset=utf-8\n\n", 40, 0);
                send(new_socket, webpageA, strlen(webpageA), 0);
                send(new_socket, webpageB, strlen(webpageB), 0);
                send(new_socket, webpageC, strlen(webpageC), 0);
                send(new_socket, webpageD, strlen(webpageD), 0);
            }
            else{
                send(new_socket, "HTTP/1.1 200 OK\n\n", 16, 0);
                send(new_socket, "Connection: close\n",18, 0);
            }
        }
        close(new_socket);
    }
    close(create_socket);
    return 0;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int ispng(char* str){
    if (strlen(str)<6) return 0;
    int i, x=0;
    for (i=0;i<strlen(str)-3;i++)
        if (strncmp(str+i,".png",4)==0) x=1;
    for (i=0;i<strlen(str)-1;i++)
        if (strncmp(str+i,"..",2)==0) x=0;
    return x;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int countskips(int len){
    int i, step=0;
    for (i=0;i<len-3;i++){
        if (bufferB[i]=='#' && bufferB[i+2]=='#'){
            bufferB[i+2]='\0';
            step += str2int(bufferB+i)-1;
            bufferB[i+2]='#';
        }
        if (bufferB[i]=='#' && bufferB[i+3]=='#'){
            bufferB[i+3]='\0';
            step += str2int(bufferB+i)-1;
            bufferB[i+3]='#';
        }
    }
    return step;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void listfiles(char *str){
    /* called by web browser to get list of server files */
    
    int count=0, bufsize=1024;
    char *i1, buffer[1024]="", buffer2[1024]="", buffer3[2048]="";
    i1 = strchr(str,'=');
    if (i1==NULL || i1[1]!='.' || strstr(str,"..")!=NULL) return;
    DIR *Dir;
    struct dirent *DirEntry;
    Dir = opendir(i1+1);
    if (Dir==NULL) return;
    DirEntry = readdir(Dir);
    while (DirEntry!=NULL){
        if (strlen(buffer)+strlen(DirEntry->d_name)+1<bufsize && DirEntry->d_name[0]!='.' && DirEntry->d_type==0x4){
            count++;
            sprintf(buffer+strlen(buffer),"%s,",DirEntry->d_name);
        }
        else if (strlen(buffer2)+strlen(DirEntry->d_name)+1<bufsize && DirEntry->d_name[0]!='.' && DirEntry->d_type==0x8)
            sprintf(buffer2+strlen(buffer2),"%s,",DirEntry->d_name);
        DirEntry = readdir(Dir);
    }
    sprintf(buffer3,"#files,%d,%s%s",count,buffer,buffer2);
    int n = 1+(int)strlen(buffer3)/80;
    webwritenline(buffer3,n);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void pushcanvas(char *str){
    /* called by webbrowser to push sg back into controls */
    
    char buffer[15];
    sprintf(buffer,"#unhide,%c,",str[5]);
    webwritenline(buffer,1);
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void setquery(char *str){
    /* called by webbrowser to set query */
    
    query = str[6]-'0';
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void setendian(char *str){
    /* called by webbrowser to set endian */
    
    webGLendian = str[7]-'0';
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void setanimate(char *str){
    /* called by webbrowser to set animate */
    
    animate = str[8]-'0';
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void setfirewall(char *str, unsigned char *ip){
    /* called by webbrowser to lock controls to that one ip address */
    
    int i;
    char buffer[40];
    if (str[9]-'0'==2){
        printf("webgui: Only accepting ip address = %d.%d.%d.%d\n",ip[0],ip[1],ip[2],ip[3]);
        for (i=0;i<4;i++) {
            firewall[2*i]=1;
            firewall[2*i+1]=ip[i];
        }
        sprintf(buffer,"#lock,%d,%d,%d,%d,",ip[0],ip[1],ip[2],ip[3]);
        webwritenline(buffer,1);
    }
    else {
        firewall[0]=0;
        printf("webgui: Accepting all ip addresses.\n");
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void releaseWebGL(char *str){
    /* called by web browser to release memory storing 3D objects */
    
    char *i1;
    i1 = strchr(str,'=');
    int i, x = i1[1] - '0';
    if (x>=3){
        x -= 3;
        if (triangles[x]!=NULL) {
            for (i=0;i<11;i++) free(triangles[x][i]);
            free(triangles[x]);
            triangles[x]=NULL;
        }
        if (lines[x]!=NULL) {
            for (i=0;i<8;i++) free(lines[x][i]);
            free(lines[x]);
            lines[x]=NULL;
        }
        if (colorsGL[x]!=NULL) {
            for (i=0;i<ncolorGL[x];i++) free(colorsGL[x][i]);
            free(colorsGL[x]);
            colorsGL[x]=NULL;
        }
        triangles[x]=NULL;
        lines[x]=NULL;
        colorsGL[x]=NULL;
        indexT[x]=0;
        indexL[x]=0;
        maxtri = starttri;
        maxlin = startlin;
        ncolorGL[x]=0;
        for (i=0;i<10;i++) tricount[x][i]=0;
        for (i=0;i<10;i++) ccount[x][i]=0;
    }
    else{
        int nx = 4;
        int ny = 1;
        int img[4] = {0,0,0,0};
        double color = 1.0;
        x += 3;
        websetcolors_(&ny,&color,&color,&color,&x);
        webimagedisplay_(&nx,&ny,img,&x);
    }
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int growtri(int x, int shrink){
    /* Grows data structure that stores triangle info for 3D object plots */
    /* if shrink==1 it shrinks instead */
    
    if (maxtri==0) maxtri = starttri;
    int i, error = 0, new_size = 2*maxtri;
    if (shrink==1) new_size = indexT[x];
    float *temp[11];
    for (i=0;i<11;i++) {
        temp[i] = triangles[x][i];
        triangles[x][i] = (float*)realloc(triangles[x][i],new_size * sizeof(float));
        if (triangles[x][i]==NULL){
            error = 1;
            triangles[x][i] = temp[i];
        }
    }
    if (error==0) maxtri = new_size;
    return error;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int growlin(int x,int shrink){
    /* Grows data structure that stores line info for 3D object plots */
    /* if shrink==1 it shrinks instead */
    
    if (maxlin==0) maxlin = startlin;
    int i, error = 0, new_size = 2*maxlin;
    if (shrink==1) new_size = indexL[x];
    float *temp[8];
    for (i=0;i<8;i++) {
        temp[i] = lines[x][i];
        lines[x][i] = (float*)realloc(lines[x][i],new_size * sizeof(float));
        if (lines[x][i]==NULL){
            error = 1;
            lines[x][i] = temp[i];
        }
    }
    if (error==0) maxlin = new_size;
    return error;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int updatedatabuffer3(int x, int endian){
    /* creates dataX.gpu to give to web browser with color as 24bit   */
    /* and vertices as single precision. This exact block of data minus */
    /* the preamble goes directly into the gpu */
    
    int db_index=0;
    int i,j,k;
    int frames[5]={5,3,2,4,1};
    if (databuffer==NULL) databuffer = (char*)malloc((9*indexT[x]+6*indexL[x])*(1+sizeof(float))+20*sizeof(int));
    int *dbi = (int*)databuffer;
    unsigned char *tempA, *tempB;
    for (i=0;i<20;i++) {
        if (endian==0) dbi[i] = dbpreamble[x][i];
        else{
            tempB = (unsigned char*)(&(dbpreamble[x][i]));
            tempA = (unsigned char*)(&(dbi[i]));
            tempA[0] = tempB[3];
            tempA[1] = tempB[2];
            tempA[2] = tempB[1];
            tempA[3] = tempB[0];
        }
    }
    float *db = (float*)(databuffer + 20*sizeof(int));
    for (k=0;k<5;k++){
        for (i=0;i<indexT[x];i++)
            if (triangles[x][10][i]==frames[k])
                for (j=0;j<9;j++) {
                    if (endian==0) db[db_index++] = triangles[x][j][i];
                    else{
                        tempB = (unsigned char*)(&(triangles[x][j][i]));
                        tempA = (unsigned char*)(&(db[db_index]));
                        tempA[0] = tempB[3];
                        tempA[1] = tempB[2];
                        tempA[2] = tempB[1];
                        tempA[3] = tempB[0];
                        db_index++;
                    }
                }
        for (i=0;i<indexL[x];i++)
            if (lines[x][7][i]==frames[k])
                for (j=0;j<6;j++) {
                    if (endian==0) db[db_index++] = lines[x][j][i];
                    else{
                        tempB = (unsigned char*)(&(lines[x][j][i]));
                        tempA = (unsigned char*)(&(db[db_index]));
                        tempA[0] = tempB[3];
                        tempA[1] = tempB[2];
                        tempA[2] = tempB[1];
                        tempA[3] = tempB[0];
                        db_index++;
                    }
                }
    }
    unsigned char *db2 = (unsigned char*)(db + db_index);
    int db_index2 = 0;
    for (k=0;k<5;k++){
        for (i=0;i<indexT[x];i++)
            if (triangles[x][10][i]==frames[k]){
                for (j=0;j<3;j++) db2[db_index2++] = (unsigned char)(255*colorsGL[x][(int)(triangles[x][9][i])-1][j]);
                for (j=0;j<3;j++) db2[db_index2++] = (unsigned char)(255*colorsGL[x][(int)(triangles[x][9][i])-1][j]);
                for (j=0;j<3;j++) db2[db_index2++] = (unsigned char)(255*colorsGL[x][(int)(triangles[x][9][i])-1][j]);
            }
        if (ccount[x][frames[k]+4]==-1)
        for (i=0;i<indexL[x];i++)
            if (lines[x][7][i]==frames[k]){
                for (j=0;j<3;j++) db2[db_index2++] = (unsigned char)(255*colorsGL[x][(int)(lines[x][6][i])-1][j]);
                for (j=0;j<3;j++) db2[db_index2++] = (unsigned char)(255*colorsGL[x][(int)(lines[x][6][i])-1][j]);
            }
    }
    return sizeof(float) * db_index + sizeof(unsigned char)*db_index2 + 20*sizeof(int);
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void updatedatabuffer(int x, int xtra){
    /* creates dataX.js to give to web browser */
    
    int databuffer_len = 0;
    int i,j,k;
    int frames[5]={5,3,2,4,1};
    if (databuffer==NULL) databuffer = (char*)malloc((432+137*indexT[x]+92*indexL[x]+300)*sizeof(char));
    strcpy(databuffer,"");
    databuffer_len += sprintf(databuffer+databuffer_len,"// vectices[%d][x] for x = 0,1 - 2,3 - 4,5 - 6,7 - 8,9 are tri,line for frame 5-3-2-4-1\n",x);
    databuffer_len += sprintf(databuffer+databuffer_len,"// colors[%d][x] are R G B for respective vertex\n\n",x);
    databuffer_len += sprintf(databuffer+databuffer_len,"vertices[%d]=[]; colors[%d]=[];\n",x,x);
    for (k=0;k<5;k++){
        databuffer_len += sprintf(databuffer+databuffer_len,"vertices[%d][%d]=[\n",x,k*2);
        for (i=0;i<indexT[x];i++){
            if (triangles[x][10][i]==frames[k]){
                for (j=0;j<9;j++) databuffer_len += sprintf(databuffer+databuffer_len,"%f,",triangles[x][j][i]);
                databuffer_len += sprintf(databuffer+databuffer_len,"\n");
            }
        }
        databuffer_len += sprintf(databuffer+databuffer_len,"];\n");
        databuffer_len += sprintf(databuffer+databuffer_len,"colors[%d][%d]=[\n",x,k*2);
        for (i=0;i<indexT[x];i++){
            if (triangles[x][10][i]==frames[k]){
                for (j=0;j<3;j++) databuffer_len += sprintf(databuffer+databuffer_len,"%d,",(unsigned char)(255*colorsGL[x][(int)(triangles[x][9][i])-1][j]));
                for (j=0;j<3;j++) databuffer_len += sprintf(databuffer+databuffer_len,"%d,",(unsigned char)(255*colorsGL[x][(int)(triangles[x][9][i])-1][j]));
                for (j=0;j<3;j++) databuffer_len += sprintf(databuffer+databuffer_len,"%d,",(unsigned char)(255*colorsGL[x][(int)(triangles[x][9][i])-1][j]));
                databuffer_len += sprintf(databuffer+databuffer_len,"\n");
            }
        }
        databuffer_len += sprintf(databuffer+databuffer_len,"];\n");
        databuffer_len += sprintf(databuffer+databuffer_len,"vertices[%d][%d]=[\n",x,k*2+1);
        for (i=0;i<indexL[x];i++){
            if (lines[x][7][i]==frames[k]){
                for (j=0;j<6;j++) databuffer_len += sprintf(databuffer+databuffer_len,"%f,",lines[x][j][i]);
                databuffer_len += sprintf(databuffer+databuffer_len,"\n");
            }
        }
        databuffer_len += sprintf(databuffer+databuffer_len,"];\n");
        if (ccount[x][frames[k]+4]!=-1) databuffer_len += sprintf(databuffer+databuffer_len,"colors[%d][%d]=[];\n",x,k*2+1);
        else{
            databuffer_len += sprintf(databuffer+databuffer_len,"colors[%d][%d]=[\n",x,k*2+1);
            for (i=0;i<indexL[x];i++){
                if (lines[x][7][i]==frames[k]){
                    for (j=0;j<3;j++) databuffer_len += sprintf(databuffer+databuffer_len,"%d,",(unsigned char)(255*colorsGL[x][(int)(lines[x][6][i])-1][j]));
                    for (j=0;j<3;j++) databuffer_len += sprintf(databuffer+databuffer_len,"%d,",(unsigned char)(255*colorsGL[x][(int)(lines[x][6][i])-1][j]));
                    databuffer_len += sprintf(databuffer+databuffer_len,"\n");
                }
            }
            databuffer_len += sprintf(databuffer+databuffer_len,"];\n");
        }
    }
    if (xtra==1) {
        databuffer_len += sprintf(databuffer+databuffer_len,"\nfor (var i=0;i<10;i++){\n vertices[%d][i]=new Float32Array(vertices[%d][i]);\n",x,x);
        databuffer_len += sprintf(databuffer+databuffer_len," colors[%d][i]=new Uint8Array(colors[%d][i]);\n};\n",x,x);
        databuffer_len += sprintf(databuffer+databuffer_len,"loaddata(%d);\n",x);
        databuffer_len += sprintf(databuffer+databuffer_len,"draw(%d);",x);
    }
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void updatewebpageD(int xtra){
    /* creates part 4 of 4 for index.html for web browser */
    
    int index=0, i, dlen=0, tm=500, ct=0;
    if (animate==1 || animate==7) tm=100;
    else if (animate==2 || animate==8) tm=50;
    else if (animate==3 || animate==9) tm=33;
    char buffer[100];
    strcpy(webpageD,"\n    function init(){;\n");
    dlen = strlen(webpageD);
    if (xtra==0) for (i=0; i<cmdct; i++)
        if (cmdc[i]==1) dlen += sprintf(webpageD+dlen,"        sbtn[%d] = '%s';\n",ct++,cmda[i]);
    dlen += sprintf(webpageD+dlen,"        sbtnCT = %d;\n",ct);
    if (animate!=0) dlen += sprintf(webpageD+dlen,"        animate=%d;\n",animate);
    dlen += sprintf(webpageD+dlen,"        resizecanvas();\n");
    if (xtra==0){
        dlen += sprintf(webpageD+dlen,"        timerId = setInterval(\"AJAX('readline.php','',1,1,0,0)\",%d);\n",tm);
        dlen += sprintf(webpageD+dlen,"        AJAX('readline.php','',1,1,0,0);\n");
        dlen += sprintf(webpageD+dlen,"        AJAX('callfunct.php','updateall',1,1,0,1);\n");
        for (i=0;i<3;i++)
            if (indexT[i]+indexL[i]>0) dlen += sprintf(webpageD+dlen,"        AJAX2(%d);\n",i);
        if (firewall[0]==1)
            dlen += sprintf(webpageD+dlen,"        fkey=1; lockip([0,%d,%d,%d,%d]);\n",firewall[1],firewall[3],firewall[5],firewall[7]);
        if (webGLendian>=1)
            dlen += sprintf(webpageD+dlen,"        ekey=1; document.getElementById('endian').style.display='inline-block';\n");
    }
    dlen += sprintf(webpageD+dlen,"        var doc = document.getElementById('text').contentWindow.document;\n");
    for (i=0; i<maxhistory; i++){
        index = (hindex+i)%maxhistory;
        if (history[index][0]!='\0') {
            dlen += sprintf(webpageD+dlen,"        doc.body.innerText+=\"");
            fixquotes(buffer,history[index]);
            dlen += sprintf(webpageD+dlen,"%s",buffer);
            dlen += sprintf(webpageD+dlen,"\\n\";\n");
        }
    }
    dlen += sprintf(webpageD+dlen,"        document.getElementById('text').contentWindow.scrollTo(0,999999);\n");
    double elapsedTime; struct timeval current;
    gettimeofday(&current,NULL);
    elapsedTime = (current.tv_sec - started.tv_sec) * 1000.0;
    elapsedTime += (current.tv_usec - started.tv_usec) / 1000.0;
    if (elapsedTime<1000){
        dlen += sprintf(webpageD+dlen,"        disablebuttons();\n");
    }
    dlen += sprintf(webpageD+dlen,"    }\n</script>\n");
    if (xtra==1){
        dlen += sprintf(webpageD+dlen,"<script src='data0.js?x=%d'></script>\n",rand());
        dlen += sprintf(webpageD+dlen,"<script src='data1.js?x=%d'></script>\n",rand());
        dlen += sprintf(webpageD+dlen,"<script src='data2.js?x=%d'></script>\n",rand());
    }
    dlen += sprintf(webpageD+dlen,"</body></html>");
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void updatewebpageD2(int x, int xtra){
    /* creates part 4 of 4 for sg for web browser */
    
    int tm=500;
    if (animate==1 || animate==7) tm=100;
    else if (animate==2 || animate==8) tm=50;
    else if (animate==3 || animate==9) tm=33;
    strcpy(webpageD,"\n    function init(){;\n");
    if (xtra==0) sprintf(webpageD+strlen(webpageD),"        timerId = setInterval(\"AJAX('readline.php?x=%d','',1,1,0,0)\",%d);\n",x,tm);
    if (xtra==0 && animate!=0) sprintf(webpageD+strlen(webpageD),"        animate=%d;\n",animate);
    sprintf(webpageD+strlen(webpageD),"        hide(%d);\n",x);
    if (indexT[x]+indexL[x]>0 && xtra==0) sprintf(webpageD+strlen(webpageD),"        AJAX2(%d);\n",x);
    sprintf(webpageD+strlen(webpageD),"        sg = 1; pane = %d;\n        resizecanvas(%d);\n",x,x);
    if (xtra==0 && firewall[0]==1)
        sprintf(webpageD+strlen(webpageD),"        fkey=1; lockip([0,%d,%d,%d,%d]);\n",firewall[1],firewall[3],firewall[5],firewall[7]);
    if (webGLendian>=1)
        sprintf(webpageD+strlen(webpageD),"        ekey=1; document.getElementById('endian').style.display='inline-block';\n");
    strcat(webpageD,"    }\n</script>\n");
    if (xtra==1) sprintf(webpageD+strlen(webpageD),"<script src='data%d.js?x=%d'></script>\n",x,rand());
    strcat(webpageD,"</body></html>");
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void updatewebpageA(int hide){
    /* creates part 1 of 4 for index.html and sg for web browser */
    /* hide=1 for sg, hide=-1 for no command buttons, hide=0 for normal */
    
    int nopt=0, ct=0, i, j, k, alen=0;
    char abbr[81], deft[81], name[81], x[80];
    char *pd="&#160&#160&#160";
    char *vis="inline-block";
    char *hid="none";
    char *cmt="\n\n<!-- Command buttons -->\n";
    
    strcpy(webpageA,"<!---------------------------------------------------------->\n");
    strcat(webpageA,"<!-- this HTML/CSS/JavaScript/AJAX/WebGL is generated by  -->\n");
    strcat(webpageA,"<!-- WEBGUI A web browser based graphical user interface  -->\n");
    strcat(webpageA,"<!-- Version: 1.0 - June 25 2017                          -->\n");
    strcat(webpageA,"<!---------------------------------------------------------->\n");
    strcat(webpageA,"<!-- Copyright (c) 2017, Christopher Deotte               -->\n");
    strcat(webpageA,"<!-- Funding: NSF DMS-1345013                             -->\n");
    strcat(webpageA,"<!-- Documentation: http://ccom.ucsd.edu/~cdeotte/webgui  -->\n");
    strcat(webpageA,"<!---------------------------------------------------------->\n\n");
    strcat(webpageA,"<html lang='en' xml:lang='en' xmlns='http://www.w3.org/1999/xhtml'>\n");
    strcat(webpageA,"<head>\n  <style> .btn{display: inline-block; padding-right: 10px; }</style>\n");
    strcat(webpageA,"  <meta http-equiv='Content-Language' content='en'>\n");
    alen = strlen(webpageA);
    alen += sprintf(webpageA+alen,"  <title>%s</title>\n</head>\n",title);
    if (hide>=1) alen += sprintf(webpageA+alen,"<body onLoad='init()' onresize='resizecanvas()'>\n\n<div id='controls' style='display:%s;width:600'>",hid);
    else alen += sprintf(webpageA+alen,"<body onLoad='init()' onresize='resizecanvas()'>\n\n<div id='controls' style='display:%s;width:600'>",vis);
    if (hide<0) return;
    alen += sprintf(webpageA+alen,"%s<div id='head' style='display:inline-block'>\n",cmt);
    for (k=0; k<cmdct; k++){
        //add command buttons to web page
        if (cmdc[k]==1) strcpy(x," style='background-color:#CCCCCC'"); else x[0]='\0';
        if (strcmp(cmdt[k],"usrcmd")==0 && cmdpct[k]==0)
            alen += sprintf(webpageA+alen,"  <div class='btn'><button id='%scmd'%s>%s %s</button></div>\n",cmda[k],x,cmdn[k],cmda[k]);
        else if (cmdpct[k]>0)
            alen += sprintf(webpageA+alen,"  <div class='btn'><button id='%scmd' onclick=\"command('%s',0)\"%s>%s %s</button><button onclick=\"toggle('%s')\" id='%sbutton'>+</button></div>\n",cmda[k],cmda[k],x,cmdn[k],cmda[k],cmda[k],cmda[k]);
        else alen += sprintf(webpageA + alen,"  <div class='btn'><button id ='%scmd' onclick=\"command('%s',0)\"%s>%s %s</button></div>\n",cmda[k],cmda[k],x,cmdn[k],cmda[k]);
        ct++;
    }
    alen += sprintf(webpageA+alen,"<br><br></div>\n\n");
    alen += sprintf(webpageA+alen,"<!-- Parameter menus and option menus -->\n");
    alen += sprintf(webpageA+alen,"<div id='box' style='position:absolute; background-color:white'>\n\n");
    char extra[5000];
    for (k=0; k<cmdct; k++)
    //add command parameter input fields to web page.
    if (cmdpct[k]>0){
        ct=0;
        int elen=0;
        strcpy(extra,"");
        alen += sprintf(webpageA+alen,"<div id='%sparameters' style='display:none'>\n%s parameters:<br>\n<table><tr>\n",cmda[k],cmdn[k]);
        for (j=0;j<cmdpct[k];j++){
            if (ct!=0 && ct%4==0) alen += sprintf(webpageA+alen,"</tr><tr>\n");
            getdeftbyindex(name,deft,abbr,&nopt,cmdp[k][j]);
            if (nt[cmdp[k][j]]=='s' || nt[cmdp[k][j]]=='l'){
                elen += sprintf(extra+elen,"</tr><tr>\n");
                if (nopt==1) elen += sprintf(extra+elen,"  <td><button onclick=\"toggle2('%s')\">%s %s</button></td>\n  <td colspan='7'><input type='text' value='%s' data='%s' data-t='%c' size=80 class='%s'>%s</td>\n",name,name,abbr,deft,deft,nt[cmdp[k][j]],name,pd);
                else elen += sprintf(extra+elen,"  <td>%s %s</td>\n  <td colspan='7'><input type='text' value='%s' data='%s' data-t='%c' size=80 class='%s'>%s</td>\n",name,abbr,deft,deft,nt[cmdp[k][j]],name,pd);
            }
            else if (nt[cmdp[k][j]]=='f'){
                elen += sprintf(extra+elen,"</tr><tr>\n");
                elen += sprintf(extra+elen,"  <td><button onclick=\"toggle3('%s')\">%s %s</button></td>\n  <td colspan='7'><input type='text' value='%s' data='%s' data-t='%c' size=80 class='%s'>%s</td>\n",name,name,abbr,deft,deft,nt[cmdp[k][j]],name,pd);
            }
            else{
                if (nopt==1) alen += sprintf(webpageA+alen,"  <td><button onclick=\"toggle2('%s')\">%s %s</button></td>\n  <td><input type='text' value='%s' data='%s' data-t='%c' size=8 class='%s'>%s</td>\n",name,name,abbr,deft,deft,nt[cmdp[k][j]],name,pd);
                else alen += sprintf(webpageA+alen,"  <td>%s %s</td>\n  <td><input type='text' value='%s' data='%s' data-t='%c' size=8 class='%s'>%s</td>\n",name,abbr,deft,deft,nt[cmdp[k][j]],name,pd);
                ct++;
            }
        }
        for (i=0;i<4-ct%4;i++) alen += sprintf(webpageA+alen,"  <td></td><td></td>\n");
        if (extra[0]!='\0') alen += sprintf(webpageA+alen,"%s",extra);
        alen += sprintf(webpageA+alen,"</tr>\n</table><br>\n</div>\n\n");
    }
    char *temp = webpageA;
    //webpageA = realloc(webpageA,strlen(webpageA)+1);
    if (webpageA==NULL) webpageA = temp;
    if (strlen(webpageA)>maxwebpage) printf("webgui: ERROR: increase maxwebpage (because of webpageA)\n");
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void updatedeft(char *str){
    /* str is formatted as str="'t a=2,b=3,c="hi there",d=4'" with null terminated */
    /* NOTE that string is inside apostrophes */
    
    int idx=0;
    char name[80], value[80];
    char *index0, *index1, *index2, *index3;
    str[strlen(str)-1]='\0';
    index0 = strchr(str,' ');
    if (index0==NULL) return;
    removespaces(index0+1,strlen(str)-(index0-str));
    index1 = strchr(index0+1,',');
    if (index1==NULL) index1=str+strlen(str);
    while (index1!=NULL){
        index2 = strchr(index0+1,'=');
        if (index2!=NULL && index2<index1){
            strncpy(name,index0+1,index2-index0-1);
            name[index2-index0-1]='\0';
            if (index2[1]=='"'){
                index3 = strchr(index2+2,'"');
                if (index3==NULL) index3=str+strlen(str);
                if (index1<index3) {
                    index1 = strchr(index3,',');
                    if (index1==NULL) index1=str+strlen(str);
                }
                strncpy(value,index2+2,index3-index2-2);
                value[index3-index2-2]='\0';
            }
            else{
                strncpy(value,index2+1,index1-index2-1);
                value[index1-index2-1]='\0';
            }
            idx = getindexbyname(name);
            value[maxnamelen]='\0';
            if (idx!=-1) strcpy(nd[idx],value);
        }
        if (index1>=str+strlen(str)) index1=NULL;
        else{
            index0 = index1;
            index1 = strchr(index1+1,',');
            if (index1==NULL) index1=str+strlen(str);
        }
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void parse(char *str, char *key, char *value){
    /* str is formatted as str="a=2,b=3,c="hi there",d=4 ". */
    /* NOTE!: it is space terminated with no spaces outside quotes. */
    
    int quote1=0, quote2=0;
    char key2[80], value2[80];
    char *i0, *i1, *i2, *i3, *i4;
    str[78]='\0';
    value[0]='\0';
    i0 = str-1;
    i3 = strchr(i0+1,' ');
    while (i3-i0>1){
        i1 = strchr(i0+1,',');
        i2 = strchr(i0+1,'=');
        if (i1==NULL || i1>i3) i1=i3;
        if (i2!=NULL && i2<i1){
            quote1 = 0; quote2 = 0;
            strncpy(key2,i0+1,i2-i0-1);
            key2[i2-i0-1]='\0';
            if (i2[1]=='"'){
                quote1 = 1; quote2 = 1;
                i4 = strchr(i2+2,'"');
                if (i4==NULL || i4>=str+80) {
                    i4=i3;
                    quote2 = 0;
                }
                if (i3<i4) i3 = strchr(i4,' ');
                if (i1<i4) i1 = strchr(i4,',');
                if (i1==NULL || i1>i3) i1=i3;
            }
            strncpy(value2,i2+1+quote1,i1-i2-1-quote1-quote2);
            value2[i1-i2-1-quote1-quote2]='\0';
            if (strcmp(key2,key)==0) strcpy(value,value2);
        }
        else if (i2==NULL) i1=i3;
        i0 = i1;
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void getdeftbyname(char *name, char *deft, char *abbr, int *nopt, int *index){
    int i;
    *index=-1;
    for (i=0; i<nct; i++){
        if (strcmp(name,nn[i])==0){
            strcpy(deft,nd[i]);
            strcpy(abbr,na[i]);
            *nopt=no[i];
            *index=i;
        }
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void getdeftbyindex(char *name, char *deft, char *abbr, int *nopt, int index){
    if (index==-1) return;
    strcpy(name,nn[index]);
    strcpy(deft,nd[index]);
    strcpy(abbr,na[index]);
    *nopt=no[index];
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int getindexbyname(char *name){
    int i;
    for (i=0; i<nct; i++)
    if (strcmp(name,nn[i])==0) return i;
    return -1;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int getindexbycmd(char *name){
    /* provide either short or long name */
    
    int i;
    for (i=0; i<cmdct; i++){
        if (strcmp(name,cmdn[i])==0) return i;
        if (strcmp(name,cmda[i])==0) return i;
    }
    return -1;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int str2int(char* str){
    int i, len, x = 0;
    len = strlen(str);
    for (i=0;i<len;i++){
        if (str[i]>='0' && str[i]<='9')
            x = x + power(10,len-i-1)*((unsigned char)str[i] - 48);
    }
    return x;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int power(int x, int y){
    /* returns x^y */
    
    int i, z=1;
    for (i=0;i<y;i++) z=z*x;
    return z;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int isint(char *str){
    int x=1, i;
    for (i=0;i<strlen(str);i++){
        if (str[i]!='-' && (str[i]<'0' || str[i]>'9')) x=0;
    }
    return x;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int isreal(char *str){
    int x=1, i;
    char c;
    for (i=0; i<strlen(str); i++){
        c = str[i];
        if ( !((c>='0' && c<='9') || c=='-' || c=='.' || c=='e' || c=='E') ) x=0;
    }
    return x;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
int isvalid(int x, char c){
    int v=1, i;
    if (x<=0) v=0;
    else for (i=0; i<nct; i++)
        if (nt[i]==c && ni[i]+1==x) v=0;
    return v;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void removespaces(char *str, int size){
    /* removes all spaces outside of quoation marks */
    
    int quote=-1;
    char *dst=str, *src=str;
    while (src<str+size){
        if (*src=='"') quote = quote * -1;
        if (*src!=' ' || quote==1){
            *dst = *src;
            dst++;
        }
        src++;
    }
    while (dst<str+size){
        *dst = ' ';
        dst++;
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void remove0e(char *str){
    /* removes e0 at end of a string */
    
    int size = strlen(str);
    if (size>=2 && str[size-2]=='e' && str[size-1]=='0') str[size-2]='\0';
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void fortran2c(char *str, int len, int quote){
    /* converts fortran string to c string */
    
    int i;
    char* idx = str+len-1;
    while ((*idx==' ' ||  *idx=='\0') && idx>=str) idx--;
    idx[1]='\0';
    if (quote==1){
        if (idx-str==len-1) idx--;
        for (i=idx-str+1;i>0;i--) str[i] = str[i-1];
        str[0] = '"';
        idx[2] = '"';
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void c2fortran(char* str, int len){
    /* converts c string to fortran string */
    
    int j, padd=0;
    for (j=0; j<len; j++) if (str[j]=='\0' || padd==1) {
        str[j]=' ';
        padd=1;
    }
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void removeapost(char *str){
    /* removes apostrophes and quotation marks from c string */
    
    char *dst=str, *src=str;
    while (src<str+strlen(str)+1){
        if (*src!='\'' && *src!='"'){
            *dst = *src;
            dst++;
        }
        src++;
    }
    while (dst<str+strlen(str)+1){
        *dst = ' ';
        dst++;
    }
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void fixquotes(char *dst, char *src){
    /* replaces quotes with backslash quote */
    
    char *indexA, *indexB;
    indexA = dst;
    indexB = src;
    while (indexB-src<strlen(src)) {
        if (*indexB=='"') {
            *indexA='\\';
            indexA++;
        }
        *indexA=*indexB++;
        indexA++;
    }
    *indexA='\0';
    return;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
unsigned long fsize(char* file){
    /* returns file size */
    
    FILE * f = fopen(file, "r");
    fseek(f, 0, SEEK_END);
    unsigned long len = (unsigned long)ftell(f);
    fclose(f);
    return len;
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void urldecode(char *dst, const char *src){
    /* converts a url string to normal string */
    
    char a, b;
    while (*src) {
        if ((*src == '%') &&
        ((a = src[1]) && (b = src[2])) &&
        (isxdigit(a) && isxdigit(b))) {
            if (a >= 'a') a -= 'a'-'A';
            if (a >= 'A') a -= ('A' - 10);
            else a -= '0';
            if (b >= 'a') b -= 'a'-'A';
            if (b >= 'A') b -= ('A' - 10);
            else b -= '0';
            *dst++ = 16*a+b;
            src+=3;
        }
        else if (*src == '+') {*dst++ = ' '; src++;}
        else *dst++ = *src++;
    }
    *dst++ = '\0';
}

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
char indexChtml[1438][172] = {
    "  Enter Command:<br>",
    "  <form onSubmit=\"AJAX('writeline.php',document.getElementById('command').value,1,1,1,0);return false;\">",
    "    <input id=\"command\" type=\"text\" name='command' size=80 autocomplete=\"off\">",
    "    <input id=\"click\" type=\"submit\" value=\"Submit\" onclick=\"\" >",
    "  </form>",
    "</div><br>",
    "",
    "<!-- Output text pane with command history -->",
    "<iframe id='text' width=600 height=400 style='background-color:#EEEEEE'></iframe>",
    "",
    "</div><!-- id='controls' -->",
    "",
    "<!-- Display panes for 3D objects and 2D images -->",
    " <div id=\"cdiv0\" style=\"display:none;border:1px solid #BBBBBB;\">",
    "    <img src=\"figure0.bmp\" id=\"figure0\" >",
    "    <button onclick=\"releasememory2(0);\" style=\"float:right;\">Free</button>",
    " </div>",
    "",
    " <div id=\"cdiv3\" style=\"display:inline-block;border:1px solid #BBBBBB;\">",
    "    <canvas id=\"my_Canvas0\"></canvas><br>",
    "    <span id=\"textD3\" style=\"color:#DDDDDD\">&#160 0 tri, 0 lin</span>",
    "    <button onclick=\"document.getElementById('filechoice0').click();\" style=\"float:right\">Load</button>",
    "    <button onclick=\"save(0);\" style=\"float:right\">Save</button>",
    "    <button id=\"pop0\" onclick=\"pop(0);\" style=\"float:right\">Pop</button>",
    "    <button id=\"spin0\" onclick=\"stopspin[0]*=-1;spin(0);\" style=\"float:right\">Spin</button>",
    "    <button onclick=\"releasememory(0);\" style=\"float:right\">Free</button>",
    "    <button onclick=\"resetposition(0);draw(0)\" style=\"float:right\">Reset</button>",
    " </div>",
    "",
    " <div id=\"cdiv1\" style=\"display:none;border:1px solid #BBBBBB;\">",
    "    <img src=\"figure1.bmp\" id=\"figure1\" >",
    "    <button onclick=\"releasememory2(1);\" style=\"float:right\">Free</button>",
    " </div>",
    "",
    " <div id=\"cdiv4\" style=\"display:inline-block;border:1px solid #BBBBBB;\">",
    "    <canvas id=\"my_Canvas1\" ></canvas>",
    "    <span id=\"textD4\" style=\"color:#DDDDDD\">&#160 0 tri, 0 lin</span>",
    "    <button onclick=\"document.getElementById('filechoice1').click();\" style=\"float:right\">Load</button>",
    "    <button onclick=\"save(1);\" style=\"float:right\">Save</button>",
    "    <button id=\"pop1\" onclick=\"pop(1);\" style=\"float:right\">Pop</button>",
    "    <button id=\"spin1\" onclick=\"stopspin[1]*=-1;spin(1);\" style=\"float:right\">Spin</button>",
    "    <button onclick=\"releasememory(1);\" style=\"float:right\">Free</button>",
    "    <button onclick=\"resetposition(1);draw(1)\" style=\"float:right\">Reset</button>",
    " </div>",
    "",
    " <div id=\"cdiv2\" style=\"display:none;border:1px solid #BBBBBB;\">",
    "    <img src=\"figure2.bmp\" id=\"figure2\" >",
    "    <button onclick=\"releasememory2(2);\" style=\"float:right\">Free</button>",
    " </div>",
    "",
    " <div id=\"cdiv5\" style=\"display:inline-block;border:1px solid #BBBBBB;\">",
    "    <canvas id=\"my_Canvas2\"></canvas>",
    "    <span id=\"textD5\" style=\"color:#DDDDDD\">&#160 0 tri, 0 lin</span>",
    "    <button onclick=\"document.getElementById('filechoice2').click();\" style=\"float:right\">Load</button>",
    "    <button onclick=\"save(2);\" style=\"float:right\">Save</button>",
    "    <button id=\"pop2\" onclick=\"pop(2);\" style=\"float:right\">Pop</button>",
    "    <button id=\"spin2\" onclick=\"stopspin[2]*=-1;spin(2);\" style=\"float:right\">Spin</button>",
    "    <button onclick=\"releasememory(2);\" style=\"float:right\">Free</button>",
    "    <button onclick=\"resetposition(2);draw(2)\" style=\"float:right\">Reset</button>",
    " </div><br><br>",
    "",
    " <div id=\"webGLcontrols\">",
    "    <input id=\"filechoice0\" type=\"file\" onchange=\"openFile(event)\" style=\"display:none\">",
    "    <input id=\"filechoice1\" type=\"file\" onchange=\"openFile(event)\" style=\"display:none\">",
    "    <input id=\"filechoice2\" type=\"file\" onchange=\"openFile(event)\" style=\"display:none\">",
    " </div>",
    "",
    " <div id=\"confirmbutton\" style=\"display:none;border-radius:10px;cursor:pointer;position:absolute;left:10px;top:10px;",
    "    color:#333333;background-color:#EEEEEE;font-size:25px;border:5px solid blue;padding:4px;z-index:3\">",
    "    <div onclick=\"confirmcontinue()\">CLICK TO CONTINUE</div>",
    " </div>",
    "",
    " <div id=\"mouseinfodiv\" style=\"display:none;border-radius:10px;position:absolute;left:10px;top:10px;",
    "    color:#333333;background-color:#EEEEEE;border:5px solid blue;padding:4px\">",
    "    <div id=\"mouseinfo\">Hello!</div>",
    " </div>",
    "",
    " <div id='locked' style=\"color:#DDDDDD\"></div>",
    " <div id='endian' style=\"color:#DDDDDD;display:none\">ENDIAN FLIP: Client is receiving flipped endianness of server.</div>",
    " <div id='animate' style=\"color:#DDDDDD\"></div>",
    " <div id='lastkey' style=\"color:#DDDDDD\"></div>",
    " <div id='lastmse' style=\"color:#DDDDDD\"></div>",
    " <div id='blackout' style=\"position:fixed;z-index:2;top:0;left:0;background:rgba(255,255,255,0.6);display:none;\">",
    "</body>",
    "",
    "<script>",
    "    /**********************************************************************************/",
    "    /* Copyright (c) 2017, Christopher Deotte                                         */",
    "    /*                                                                                */",
    "    /* Permission is hereby granted, free of charge, to any person obtaining a copy   */",
    "    /* of this software and associated documentation files (the \"Software\"), to deal  */",
    "    /* in the Software without restriction, including without limitation the rights   */",
    "    /* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell      */",
    "    /* copies of the Software, and to permit persons to whom the Software is          */",
    "    /* furnished to do so, subject to the following conditions:                       */",
    "    /*                                                                                */",
    "    /* The above copyright notice and this permission notice shall be included in all */",
    "    /* copies or substantial portions of the Software.                                */",
    "    /*                                                                                */",
    "    /* THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR     */",
    "    /* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,       */",
    "    /* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE    */",
    "    /* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER         */",
    "    /* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,  */",
    "    /* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE  */",
    "    /* SOFTWARE.                                                                      */",
    "    /**********************************************************************************/",
    "",
    "    /***************************************************************************/",
    "    /* this HTML/CSS/JavaScript/AJAX/WebGL is generated by                     */",
    "    /* WEBGUI A web browser based graphical user interface                     */",
    "    /* Version: 1.0 - June 25 2017                                             */",
    "    /***************************************************************************/",
    "    /* Author: Christopher Deotte                                              */",
    "    /* Advisor: Randolph E. Bank                                               */",
    "    /* Funding: NSF DMS-1345013                                                */",
    "    /* Documentation: http://ccom.ucsd.edu/~cdeotte/webgui                     */",
    "    /***************************************************************************/",
    "    ",
    "    var variable = '', prefix = '', sbtn=[], sbtnCT=0, active=0, firstresize=1;",
    "    var isChrome = /Chrome/.test(navigator.userAgent) && /Google Inc/.test(navigator.vendor);",
    "    var isSafari = /Safari/.test(navigator.userAgent) && /Apple Computer/.test(navigator.vendor);",
    "    var isMobile = 0; checkMobile();",
    "    window.onscroll = function(){",
    "        document.getElementById(\"confirmbutton\").style.top = document.body.scrollTop + 10;",
    "    }",
    "    window.onfocus = enablebuttons;",
    "    window.onblur = disablebuttons;",
    "    document.getElementById('text').contentWindow.onfocus = enablebuttons;",
    "    document.getElementById('text').contentWindow.onblur = disablebuttons;",
    "    function disablebuttons(){",
    "        if (sg==-1) document.getElementById(\"blackout\").style.display=\"\";",
    "    }",
    "    function enablebuttons(){",
    "        if (document.getElementById(\"confirmbutton\").style.display!=\"block\")",
    "            document.getElementById(\"blackout\").style.display=\"none\";",
    "    }",
    "    function command(x,z){",
    "        /* process and filter user supplied command string before sending to server */",
    "        var text='';",
    "        var div = document.getElementById(x+'parameters');",
    "        if (div){",
    "            var inputs = div.getElementsByTagName('input');",
    "            for (var i=0; i<inputs.length; i++){",
    "                if (inputs[i].hasAttribute('class'))",
    "                if (inputs[i].value!=inputs[i].getAttribute('data')){",
    "                    inputs[i].value = inputs[i].value.replace(/\\\"/g,\"\");",
    "                    inputs[i].value = inputs[i].value.replace(/\\'/g,\"\");",
    "                    if (text!='') text=text+',';",
    "                    else text=text+' ';",
    "                    if (inputs[i].getAttribute('data-t')=='l') text=text+''+inputs[i].getAttribute('class')+'=\"'+inputs[i].value+'\"';",
    "                    else {",
    "                        var err=0;",
    "                        inputs[i].value = inputs[i].value.replace(/ /g,\"\");",
    "                        inputs[i].value = inputs[i].value.replace(/,/g,\"\");",
    "                        if (inputs[i].getAttribute('data-t')=='i' || inputs[i].getAttribute('data-t')=='r')",
    "                            inputs[i].value = inputs[i].value.replace(/\\+/g,\"\");",
    "                        if (inputs[i].getAttribute('data-t')=='i' && isint(inputs[i].value)==0) err=1;",
    "                        if (inputs[i].getAttribute('data-t')=='r' && isreal(inputs[i].value)==0) err=1;",
    "                        if (err==1){",
    "                            alert(\"ERROR: variable '\"+inputs[i].getAttribute('class')+\"' should be type \"+gettype(inputs[i].getAttribute('data-t')));",
    "                            return -1;",
    "                        }",
    "                        text=text+''+inputs[i].getAttribute('class')+'='+inputs[i].value;",
    "                    }",
    "                    var items = document.getElementsByClassName(inputs[i].getAttribute('class'));",
    "                    for (var j=0; j<items.length; j++){",
    "                        items[j].setAttribute('data',inputs[i].value);",
    "                        items[j].value=inputs[i].value;",
    "                    }",
    "                }",
    "            }",
    "        }",
    "        var i1;",
    "        if (z==0 && closeall()==-1) return -1;",
    "        while (text.length>60){",
    "            i1=60;",
    "            while (i1>=0 && (text.charAt(i1)!=',' || insideComma(text,i1) )) i1--;",
    "            AJAX('writeline.php',x.toUpperCase()+text.substring(0,i1),1,1,1,0);",
    "            text = \" \"+text.substring(i1+1);",
    "        }",
    "        if (z==1) {if (text!='') {",
    "            document.getElementById('command').value=x.toUpperCase()+text;",
    "            AJAX('writeline.php',x.toUpperCase()+text,1,1,1,0);",
    "        }}",
    "        else {",
    "            document.getElementById('command').value=x+text;",
    "            AJAX('writeline.php',x+text,1,1,1,0);",
    "        }",
    "    }",
    "    function AJAX(url,data,get,asy,clear,funct){",
    "        /* request and post commands to server */",
    "        if (clear) {",
    "            document.getElementById('command').value='';",
    "            var doc = document.getElementById('text').contentWindow.document;",
    "            prefix=''; variable='';",
    "            doc.body.innerText+=\"command:\"+data+\"\\n\";",
    "            document.getElementById('text').contentWindow.scrollTo(0,999999);",
    "        }",
    "        ",
    "        var page_request = false",
    "        if (window.XMLHttpRequest) // if Mozilla, Safari etc",
    "            page_request = new XMLHttpRequest();",
    "        else if (window.ActiveXObject){ // if older IE",
    "            try {page_request = new ActiveXObject(\"Msxml2.XMLHTTP\")}catch (e){",
    "                try{page_request = new ActiveXObject(\"Microsoft.XMLHTTP\")}catch (e){}",
    "            }",
    "        }",
    "        else return false",
    "        ",
    "        if(asy){",
    "            page_request.onreadystatechange=function(){",
    "                if (page_request.readyState==4 && page_request.status==200){",
    "                    var str=\"\"; try{str+=page_request.responseText;}catch(err){};",
    "                    var doc = document.getElementById('text').contentWindow.document;",
    "                    if (str!='') {",
    "                        while (str.indexOf(\"#\")!=-1) str = processcmd(str);",
    "                        if (str!=''){",
    "                            while (str!=''){",
    "                                doc.body.innerText+=str.substring(0,80)+\"\\n\";",
    "                                str = str.substring(80);",
    "                            }",
    "                            document.getElementById('text').contentWindow.scrollTo(0,999999);",
    "                        }",
    "                    }",
    "                }",
    "            };",
    "        }",
    "        if (!get) page_request.open('POST', url, asy);",
    "        else if (data=='') page_request.open('GET', url, asy);",
    "        else if (funct==0) page_request.open('GET', url+\"?cmd='\"+data+\"'\", asy);",
    "        else page_request.open('GET', url+\"?\"+data, asy);",
    "        page_request.setRequestHeader('Content-Type','application/x-www-form-urlencoded');",
    "        page_request.send(data);",
    "        if (url=='writeline.php') active = 1;",
    "        var strResult='';",
    "        if (!asy) strResult=page_request.responseText;",
    "        return strResult;",
    "    }",
    "    function openFile(event){",
    "        /* load WebGL object to display from local machine */",
    "        input = event.target;",
    "        var istr = input.value;",
    "        if (istr.indexOf('.gpu')==-1) {",
    "            alert(\"Can only load *.gpu files\");",
    "            input.value='';",
    "            return;",
    "        }",
    "        AJAX2(-1*parseInt(input.id[10])-1);",
    "    }",
    "    function AJAX2(k){",
    "        /* request WebGL data from server for gpu display */",
    "        /* or read WebGL data from local file */",
    "        var local = 0, oReq;",
    "        if (k<0){",
    "            k=-k-1;",
    "            local = 1;",
    "        }",
    "        if (local==0) {",
    "            oReq = new XMLHttpRequest();",
    "            oReq.open(\"GET\", \"data\"+k+\".gpu\", true);",
    "            oReq.responseType = \"arraybuffer\";",
    "        }",
    "        else oReq = new FileReader();",
    "        oReq.onload = function (oEvent) {",
    "            var arrayBuffer;",
    "            if (local==0) arrayBuffer = oReq.response;",
    "            else arrayBuffer = oReq.result;",
    "            var csize = 1;",
    "            if (arrayBuffer) {",
    "                var argv = new Int32Array(arrayBuffer, 0, 20);",
    "                var ts = 9; offset = 80;",
    "                for (var i=1;i<11;i++){",
    "                    if (i%2==0) ts = 6;",
    "                    else ts = 9;",
    "                    vertices[k][i-1] = new Float32Array(arrayBuffer, offset, ts * argv[i-1]);",
    "                    offset += 4 * ts * argv[i-1];",
    "                }",
    "                for (var i=1;i<11;i++){",
    "                    if (i%2==0) ts = 6;",
    "                    else ts = 9;",
    "                    colors[k][i-1] = new Uint8Array(arrayBuffer, offset, ts * argv[i+9]);",
    "                    offset += csize * ts * argv[i+9];",
    "                }",
    "                loaddata(k);",
    "                draw(k);",
    "            }",
    "        };",
    "        if (local==0) oReq.send(null);",
    "        else{",
    "          oReq.readAsArrayBuffer(input.files[0]);",
    "          input.value='';",
    "        }",
    "    }",
    "    function processcmd(str){",
    "        /* intrepret command from server. Either text to display or command to execute */",
    "        var cmd, i1, i2, argv, argc, i, key, val;",
    "        var s = 80, i3=-1;",
    "        i1 = str.indexOf(\"#\");",
    "        i2 = i1+1+str.substring(i1+1).indexOf(\"#\");",
    "        i3 = i1;",
    "        if (i2!=i1 && i2-i1<=3) {",
    "            s = 80 * parseInt(str.substring(i1+1,i2));",
    "            i1 = i2;",
    "        }",
    "        if (i1!=-1){",
    "            cmd = str.substring(i1+1,i3+s);",
    "            //argv = cmd.split(\",\");",
    "            argv = customSplit(cmd);",
    "            argc = argv.length;",
    "            if (cmd.substring(0,5)=='image') {",
    "            /* display a static image */",
    "                if (argc==5) {",
    "                    var k = parseInt(argv[3]);",
    "                    document.getElementById('figure'+argv[3]).width=getWidth(0);",
    "                    document.getElementById('figure'+argv[3]).height=getWidth(0)*2/3;",
    "                    if (popped[k]==0) {",
    "                        releasememory(k);",
    "                        document.getElementById('cdiv'+(parseInt(argv[3])+3)).style.display='none';",
    "                        document.getElementById('cdiv'+argv[3]).style.display='inline-block';",
    "                        document.getElementById('figure'+argv[3]).src='figure'+argv[3]+'.bmp?'+Math.random();",
    "                    }",
    "                }",
    "            }",
    "            else if (cmd.substring(0,6)=='webgl2') {",
    "            /* display a dynamic webGL object */",
    "                if (argc==3) {",
    "                    var k = parseInt(argv[1]);",
    "                    if (webgl==0) {",
    "                        alert (\"Unable to initialize WebGL. Enable WebGL in your browser.\");",
    "                        AJAX('callfunct.php','release='+(k+3),1,1,0,1);",
    "                    }",
    "                    if (popped[k]==0) {",
    "                        releasememory2(k);",
    "                        AJAX2(k);",
    "                    }",
    "                    else popped[k]=2;",
    "                }",
    "            }",
    "            else if (cmd.substring(0,6)=='button' && argc==4){",
    "            /* toggle color of a command button */",
    "                if (argv[2]!='') {",
    "                    document.getElementById(argv[1]+'cmd').style.backgroundColor = \"#999999\";",
    "                    sbtn[sbtnCT] = argv[1];",
    "                    sbtnCT++;",
    "                }",
    "                else {",
    "                    document.getElementById(argv[1]+'cmd').style.backgroundColor = \"#EEEEEE\";",
    "                    buttonRemove(argv[1]);",
    "                }",
    "            }",
    "            else if (cmd.substring(0,5)=='pause'){",
    "            /* prompt user to continue */",
    "                document.getElementById(\"confirmbutton\").style.top = document.body.scrollTop+10;",
    "                document.getElementById(\"confirmbutton\").style.display=\"block\";",
    "                document.getElementById(\"blackout\").style.display=\"\";",
    "            }",
    "            else if (cmd.substring(0,7)=='animate') {",
    "            /* changes animate variable */",
    "                animate = parseInt(argv[1]);",
    "                setAnimate();",
    "            }",
    "            else if (cmd.substring(0,5)=='start'){",
    "            /* server calls this when it is started */",
    "                if (active==1) location.reload(); else active = 1;",
    "            }",
    "            else if (cmd.substring(0,6)=='unhide'){",
    "            /* an sg pop out is being pushed back into controls */",
    "                unhide(parseInt(argv[1]));",
    "            }",
    "            else if (cmd.substring(0,4)=='lock'){",
    "                if (argc==6) lockip(argv);",
    "            }",
    "            else if (cmd.substring(0,6)=='update'){",
    "            /* server is updating variables */",
    "                for (i=1;i<argc-1;i++){",
    "                    i2 = argv[i].indexOf(\"=\");",
    "                    key = argv[i].substring(0,i2);",
    "                    val = argv[i].substring(i2+1);",
    "                    update(key,val,1);",
    "                }",
    "            }",
    "            else if (cmd.substring(0,5)=='files' && argc>=2){",
    "            /* display files on server */",
    "                var dirnum = parseInt(argv[1]);",
    "                var newtext = \"<html><body> \"+variable+\" options:<br>\";",
    "                newtext += \"<em>Directory .\"+prefix.substring(1)+\"/</em><br>\";",
    "                if (prefix!='.') newtext += \"<a href='javascript:parent.getdir(\\\"..\\\");' style='text-decoration:none'>&#160<img src='up.png'>..</a><br>\";",
    "                for (i=2;i<dirnum+2;i++)",
    "                    newtext+= \"<a href='javascript:parent.getdir(\\\"\"+argv[i]+\"\\\");' style='text-decoration:none'>&#160<img src='folder.png'>\"+argv[i]+\"</a><br>\";",
    "                for (i=dirnum+2;i<argc-1;i++)",
    "                    newtext+= \"<a href=\\\"javascript:parent.setValue2('\"+argv[i]+\"');\\\" style='text-decoration:none'>&#160<img src='file.png'>\"+argv[i]+\"</a><br>\";",
    "                document.getElementById('text3').contentWindow.document.open();",
    "                document.getElementById('text3').contentWindow.document.write(newtext);",
    "                document.getElementById('text3').contentWindow.document.close();",
    "                document.getElementById('text3').contentWindow.scrollTo(0,0);",
    "                var width = getWidth(0);",
    "                if (width>600) document.getElementById('text3').contentDocument.body.style.fontSize = width / 35;",
    "                else document.getElementById('text3').contentDocument.body.style.fontSize = \"\";",
    "                document.getElementById('text3').contentWindow.onfocus = enablebuttons;",
    "                document.getElementById('text3').contentWindow.onblur = disablebuttons;",
    "            }",
    "        }",
    "        return str.substring(0,i3)+str.substring(i3+s);",
    "    }",
    "    function customSplit(cmd){",
    "        /* splits cmd at commas but preserves strings in quotes that include commas */",
    "        var parts = [];",
    "        var i1=0, i2, i3, i4=0;",
    "        i2=cmd.indexOf(\",\");",
    "        i3=cmd.indexOf('\"');",
    "        while (i2!=-1){",
    "            if (i2<i3 || i3==-1) {",
    "                parts.push(cmd.substring(i1,i2));",
    "            }",
    "            else {",
    "                i4 = cmd.indexOf('\"',i3+1);",
    "                parts.push(cmd.substring(i1,i4+1).replace(/\\\"/g,\"\"));",
    "                i2 = i4+1;",
    "            }",
    "            i1 = i2+1;",
    "            i2 = cmd.indexOf(\",\",i1);",
    "            i3 = cmd.indexOf('\"',i1);",
    "        }",
    "        parts.push(cmd.substring(i1));",
    "        return parts;",
    "    }",
    "    function insideComma(text,i1){",
    "        /* determines if comma at i1 is inside quotes */",
    "        var inside = -1;",
    "        var output = false;",
    "        for (var i=0; i<text.length; i++){",
    "            if (text.charAt(i)=='\"') inside = inside * -1;",
    "            if (i==i1 && text.charAt(i)==',' && inside==1) output = true;",
    "        }",
    "        return output;",
    "    }",
    "    function confirmcontinue(){",
    "        document.getElementById(\"confirmbutton\").style.display=\"none\";",
    "        document.getElementById(\"blackout\").style.display=\"none\";",
    "        AJAX('callfunct.php',\"continue=1\",1,1,0,1);",
    "    }",
    "    function resetall(){",
    "        var inputs = document.getElementsByTagName('input');",
    "        for (var i=0; i<inputs.length; i++)",
    "        if (inputs[i].hasAttribute('class'))",
    "            inputs[i].value=inputs[i].getAttribute('data');",
    "    }",
    "    function update(key, val, x){",
    "        var items = document.getElementsByClassName(key);",
    "        for (var i=0; i<items.length; i++) {",
    "            items[i].value=val;",
    "            if (x==1) items[i].setAttribute('data',val);",
    "        }",
    "    }",
    "    function gettype(c){",
    "        if (c=='i') return \"int\";",
    "        if (c=='r') return \"real\";",
    "    }",
    "    function isint(str){",
    "        if (str.length==0) return 0;",
    "        var x=1;",
    "        for (var i=0;i<str.length;i++){",
    "            var c = str.charAt(i);",
    "            if (c!='-' && (c<'0' || c>'9')) x=0;",
    "        }",
    "        return x;",
    "    }",
    "    function isreal(str){",
    "        if (str.length==0) return 0;",
    "        var x=1;",
    "        for (var i=0;i<str.length;i++){",
    "            var c = str.charAt(i);",
    "            if (c!='.' && c!='E' && c!='e' && c!='-' && (c<'0' || c>'9')) x=0;",
    "        }",
    "        return x;",
    "    }",
    "    function toggle(x){",
    "        /* show hide parameters */",
    "        if (document.getElementById(x+\"parameters\").style.display=='none') {",
    "            if (closeall()==-1) return;",
    "            document.getElementById('box').style.border=\"2px solid red\";",
    "            document.getElementById('box').style.padding=\"5px\";",
    "            document.getElementById(x+\"parameters\").style.display='inline';",
    "            document.getElementById(x+\"button\").textContent=\"-\";",
    "        }",
    "        else closeall();",
    "    }",
    "    function toggle2(x){",
    "        /* show hide non-file options */",
    "        if (document.getElementById(x+\"options\").style.display=='none') {",
    "            closeoptions();",
    "            var items = document.getElementsByName(x+\"radio\");",
    "            var items2 = document.getElementsByClassName(x);",
    "            var value = items2[0].value;",
    "            for (var i=0; i<items.length; i++){",
    "                if (items[i].value==value) items[i].checked=true;",
    "                else items[i].checked=false;",
    "            }",
    "            document.getElementById(x+\"options\").style.display='block';",
    "        }",
    "        else closeoptions();",
    "    }",
    "    function toggle3(x){",
    "        /* show hide file options */",
    "        if (document.getElementById(\"text2\").style.display=='none'){",
    "            closeoptions();",
    "            variable = x; prefix = '.';",
    "            document.getElementById(\"text2\").style.display='block';",
    "            getdir('.');",
    "        }",
    "        else closeoptions();",
    "    }",
    "    function getdir(x){",
    "        /* get list of files on server */",
    "        var i, j=-1;",
    "        if (x=='..'){",
    "            i = prefix.indexOf(\"/\");",
    "            while (i!=j){",
    "                j = i;",
    "                i = i+1+prefix.substring(i+1).indexOf(\"/\");",
    "            }",
    "            if (j!=-1) prefix = prefix.substring(0,j);",
    "        }",
    "        else if (x!='' && x!='.') prefix = prefix + \"/\" + x;",
    "        AJAX('callfunct.php','listfiles='+prefix,1,1,0,1);",
    "    }",
    "    function closefileoptions(){",
    "        prefix=''; variable='';",
    "        document.getElementById(\"text2\").style.display='none';",
    "    }",
    "    function closeoptions(){",
    "        closefileoptions();",
    "        var divs = document.getElementsByTagName('div');",
    "        for (var i=0; i<divs.length; i++)",
    "            if (divs[i].id.indexOf('options')!=-1) divs[i].style.display='none';",
    "    }",
    "    function closeall(){",
    "        closeoptions();",
    "        var divs = document.getElementsByTagName('div');",
    "        for (var i=0; i<divs.length; i++){",
    "            if (divs[i].id.indexOf('parameters')!=-1)",
    "            if (divs[i].style.display=='inline'){",
    "                var inputs = divs[i].getElementsByTagName('input');",
    "                for (var j=0; j<inputs.length; j++)",
    "                if (inputs[j].hasAttribute('class'))",
    "                    update(inputs[j].getAttribute('class'),inputs[j].value,0);",
    "                var c = divs[i].id.substring(0,divs[i].id.indexOf('parameters'));",
    "                if (command(c,1)==-1) return -1;",
    "                divs[i].style.display='none';",
    "            }",
    "        }",
    "        var buttons = document.getElementsByTagName('button');",
    "        for (var i=0; i<buttons.length; i++)",
    "            if (buttons[i].textContent=='-') buttons[i].textContent='+';",
    "        document.getElementById('box').style.border=\"\";",
    "        document.getElementById('box').style.padding=\"\";",
    "    }",
    "    function setValue(x){",
    "        /* radio set option */",
    "        var id=x.name.substring(0,x.name.length-5);",
    "        var items = document.getElementsByClassName(id);",
    "        for (var i=0; i<items.length; i++) items[i].value=x.value;",
    "        closeoptions();",
    "    }",
    "    function setValue2(x){",
    "        /* set fileoption */",
    "        var items = document.getElementsByClassName(variable);",
    "        for (var i=0; i<items.length; i++) items[i].value=prefix+\"/\"+x;",
    "        closefileoptions();",
    "        return false;",
    "    }",
    "    function buttonColored(cd){",
    "        var yes = 0;",
    "        for (var k=0;k<sbtnCT;k++)",
    "            if (cd==sbtn[k]+'cmd') yes=1;",
    "        return yes;",
    "    }",
    "    function buttonRemove(cd){",
    "        var idx=-1;",
    "        for (var k=0;k<sbtnCT;k++)",
    "            if (cd=sbtn[k]) idx=k;",
    "        if (idx!=-1) {",
    "            sbtn[idx]=sbtn[sbtnCT-1];",
    "            sbtnCT--;",
    "        }",
    "    }",
    "    /***************************************************************************/",
    "    /* this HTML/CSS/JavaScript/AJAX/WebGL is generated by                     */",
    "    /* WEBGUI A web browser based graphical user interface                     */",
    "    /* Version: 1.0 - June 25 2017                                             */",
    "    /***************************************************************************/",
    "    /* Copyright (c) 2017, Christopher Deotte                                  */",
    "    /* Funding: NSF DMS-1345013                                                */",
    "    /* Documentation: http://ccom.ucsd.edu/~cdeotte/webgui                     */",
    "    /***************************************************************************/",
    "    ",
    "    /***************************************************************************/    ",
    "    /* Code for WebGL 3D object display and manipulation below                 */",
    "    /***************************************************************************/",
    "    var vertices=[], colors=[];",
    "    for (var i=0;i<3;i++){",
    "        vertices[i]=[];",
    "        colors[i]=[];",
    "        for (var j=0;j<10;j++){",
    "            vertices[i][j]=[];",
    "            colors[i][j]=[];",
    "        }",
    "    }",
    "    var rmatrix=[], rmatrix_old=[], zoom=[1,1,1], x_trans=[0,0,0], y_trans=[0,0,0];",
    "    rmatrix_old[0]=[], rmatrix_old[1]=[], rmatrix_old[2]=[];",
    "    rmatrix[0]=[1,0,0,0,1,0,0,0,1], rmatrix[1]=[1,0,0,0,1,0,0,0,1], rmatrix[2]=[1,0,0,0,1,0,0,0,1];",
    "    var canvas=[], gl=[]; popped=[0,0,0];",
    "    var vertex_buffer=[], color_buffer=[];",
    "    var vertCode, vertShader=[], fragCode, fragShader=[], shaderProgram=[];",
    "    var vertCode2, vertShader2=[], fragCode2, fragShader2=[], shaderProgram2=[];",
    "    var coord = [], color = [], M1 = [], V1 = [];",
    "    var coord2 = [], M2 = [], V2 = [];",
    "    var drawing=[0,0,0], drag=[], old_x=[], old_y=[];",
    "    var old2_x=[0,0,0], old2_y=[0,0,0], old3_x=[0,0,0], old3_y=[0,0,0];",
    "    var oldtimestamp=[0,0,0], stopspin=[1,1,1];",
    "    var old_dx=[-3,-3,-3], old_dy=[6,6,6], old_u=[], old_d=[-1,-1,-1];",
    "    old_u[0]=[0.7071,0.7071,0], old_u[1]=[0.7071,0.7071,0], old_u[2]=[0.7071,0.7071,0];",
    "    var identity = new Float32Array([1.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,1.0]);",
    "    var webgl=0, sg=-1, ikey=-1, fkey=-1, ekey=-1, wkey=1, focus = 0, animate=0, reset=0;",
    "    var timerId=0, pane=-1, pkey=-1, btnfix=0;",
    "    if (isMobile) wkey = -1;",
    "    var optionkey=0, commandkey=0;",
    "    ",
    "    for (var i=0; i<3; i++){",
    "        /* prepare the canvas and get webgl context */",
    "        canvas[i] = document.getElementById('my_Canvas'+i);",
    "        gl[i] = canvas[i].getContext('webgl') || canvas[i].getContext('experimental-webgl');",
    "        if (!gl[i]) {",
    "            for (var k=0;k<3;k++){",
    "                document.getElementById('cdiv'+k).style.display='inline-block';",
    "                document.getElementById('cdiv'+(k+3)).style.display='none';",
    "            }",
    "            document.getElementById('webGLcontrols').style.display='none';",
    "            ",
    "        }",
    "        else{",
    "            /* store geometry and colors in buffer objects */",
    "            webgl = 1;",
    "            vertex_buffer[i] = [];",
    "            color_buffer[i] = [];",
    "            for (var k=0; k<10; k++){",
    "                vertex_buffer[i][k] = gl[i].createBuffer();",
    "                color_buffer[i][k] = gl[i].createBuffer();",
    "            }",
    "            loaddata(i);",
    "",
    "            /* create and compile shader programs */",
    "            vertCode =",
    "                'attribute vec3 coordinates;' +",
    "                'attribute vec3 color;' +",
    "                'varying mediump vec3 vColor;' +",
    "                'uniform mat3 M1;' +",
    "                'uniform vec3 V1;' +",
    "                'void main(void) {' +",
    "                    ' gl_Position = vec4( M1 * coordinates + V1, 1.0);' +",
    "                    ' gl_Position.z = 0.0001 * gl_Position.z;' +",
    "                    ' vColor = color;' +",
    "                '}';",
    "            vertShader[i] = gl[i].createShader(gl[i].VERTEX_SHADER);",
    "            gl[i].shaderSource(vertShader[i], vertCode);",
    "            gl[i].compileShader(vertShader[i]);",
    "            fragCode =",
    "                'varying mediump vec3 vColor;' +",
    "                'void main(void) {' +",
    "                    ' gl_FragColor = vec4(vColor, 1.0);' +",
    "                '}';",
    "            fragShader[i] = gl[i].createShader(gl[i].FRAGMENT_SHADER);",
    "            gl[i].shaderSource(fragShader[i], fragCode);",
    "            gl[i].compileShader(fragShader[i]);",
    "            shaderProgram[i] = gl[i].createProgram();",
    "            gl[i].attachShader(shaderProgram[i], vertShader[i]);",
    "            gl[i].attachShader(shaderProgram[i], fragShader[i]);",
    "            gl[i].linkProgram(shaderProgram[i]);",
    "            ",
    "            vertCode2 =",
    "                'attribute vec3 coordinates;' +",
    "                'uniform mat3 M1;' +",
    "                'uniform vec3 V1;' +",
    "                'void main(void) {' +",
    "                    ' gl_Position = vec4( M1 * coordinates + V1, 1.0);' +",
    "                    ' gl_Position.z = 0.0001 * gl_Position.z;' +",
    "                '}';",
    "            vertShader2[i] = gl[i].createShader(gl[i].VERTEX_SHADER);",
    "            gl[i].shaderSource(vertShader2[i], vertCode2);",
    "            gl[i].compileShader(vertShader2[i]);",
    "            fragCode2 =",
    "                'void main(void) {' +",
    "                    ' gl_FragColor = vec4(0.0, 0.0, 0.0, 1.0);' +",
    "                '}';",
    "            fragShader2[i] = gl[i].createShader(gl[i].FRAGMENT_SHADER);",
    "            gl[i].shaderSource(fragShader2[i], fragCode2);",
    "            gl[i].compileShader(fragShader2[i]);",
    "            shaderProgram2[i] = gl[i].createProgram();",
    "            gl[i].attachShader(shaderProgram2[i], vertShader2[i]);",
    "            gl[i].attachShader(shaderProgram2[i], fragShader2[i]);",
    "            gl[i].linkProgram(shaderProgram2[i]);",
    "",
    "            ",
    "            /* get shader programs variable references */",
    "            coord[i] = gl[i].getAttribLocation(shaderProgram[i], \"coordinates\");",
    "            color[i] = gl[i].getAttribLocation(shaderProgram[i], \"color\");",
    "            M1[i] = gl[i].getUniformLocation(shaderProgram[i], \"M1\");",
    "            V1[i] = gl[i].getUniformLocation(shaderProgram[i], \"V1\");",
    "            ",
    "            coord2[i] = gl[i].getAttribLocation(shaderProgram2[i], \"coordinates\");",
    "            M2[i] = gl[i].getUniformLocation(shaderProgram2[i], \"M1\");",
    "            V2[i] = gl[i].getUniformLocation(shaderProgram2[i], \"V1\");",
    "            ",
    "            /* draw the 5 frames/lists with their polygons and lines */",
    "            draw(i);",
    "            ",
    "            /* Add mouse rotation, scale, translation controls */",
    "            drag[i] = -1; old_x[i] = 0; old_y[i] = 0;",
    "            canvas[i].addEventListener(\"contextmenu\",contextMenu,false);",
    "            canvas[i].addEventListener(\"mousedown\", mouseDown, false);",
    "            canvas[i].addEventListener(\"mouseup\", mouseUp, false);",
    "            canvas[i].addEventListener(\"mouseout\", mouseUp, false);",
    "            canvas[i].addEventListener(\"mousemove\", mouseMove, false);",
    "        }",
    "    }",
    "    document.addEventListener(\"keydown\", keyDown, false);",
    "    document.addEventListener(\"keyup\", keyUp, false);",
    "    document.getElementById(\"figure0\").addEventListener(\"mousedown\", mouseDown2, false);",
    "    document.getElementById(\"figure0\").addEventListener(\"contextmenu\",function(e){e.preventDefault();return false;},false);",
    "    document.getElementById(\"figure1\").addEventListener(\"mousedown\", mouseDown2, false);",
    "    document.getElementById(\"figure2\").addEventListener(\"mousedown\", mouseDown2, false);",
    "    ",
    "    function loaddata(k){",
    "        /* move gpu data from javascript into gpu */",
    "        if (webgl==0) return;",
    "        if (animate==0) resetposition(k);",
    "        if (animate>=4 && animate<=6 && reset==1) resetposition(k);",
    "        for (var i=0; i<10; i++){",
    "            gl[k].bindBuffer(gl[k].ARRAY_BUFFER, vertex_buffer[k][i]);",
    "            gl[k].bufferData(gl[k].ARRAY_BUFFER, vertices[k][i], gl[k].STATIC_DRAW);",
    "            gl[k].bindBuffer(gl[k].ARRAY_BUFFER, null);",
    "            gl[k].bindBuffer(gl[k].ARRAY_BUFFER, color_buffer[k][i]);",
    "            gl[k].bufferData(gl[k].ARRAY_BUFFER, colors[k][i], gl[k].STATIC_DRAW);",
    "            gl[k].bindBuffer(gl[k].ARRAY_BUFFER, null);",
    "        }",
    "    }",
    "    function draw(k){",
    "        // draws all the objects",
    "        if (webgl==0) return;",
    "        gl[k].clearColor(1.0, 1.0, 1.0, 1.0);",
    "        gl[k].enable(gl[k].DEPTH_TEST);",
    "        gl[k].clear(gl[k].COLOR_BUFFER_BIT);",
    "        gl[k].viewport(0, 0, canvas[k].width, canvas[k].height);",
    "        if (getobjectcount(k)==0) return;",
    "        ",
    "        /* Mouse rotation, scale, and translation */",
    "        /* position = scale * (scale2 * rotate2  * (coordinates + translate2) + translate) + translate3 */",
    "        /* p = vA * (vB * mC * (x + vE) + vD) + vF  */",
    "        /* Note: VertexShader multiplies vectors on left of matrices */",
    "        ",
    "        var vA=[], vB=[], mC=[], vD=[], vE=[], vF=[], mG=[], vH=[];",
    "        vA=[zoom[k],zoom[k],zoom[k]];",
    "        mC=rmatrix[k];",
    "        vD=[2.0*x_trans[k]/canvas[k].width,-2.0*y_trans[k]/canvas[k].height,0];",
    "        vE=[-0.5,-0.5,-0.5];",
    "        ",
    "        /* draw polygons and lines for frames/lists 5,3,2,4,1 */",
    "        for (var i=0;i<5;i++){",
    "            if (i==0 || i==3 || i==4){",
    "                vF=[-1/3,0,0];",
    "                vB=[4/3,2,-2];",
    "            }",
    "            else if (i==1){",
    "                vF=[2/3,-0.5,0.02];",
    "                vB=[2/3,1,-1];",
    "                mC=[1,0,0,0,1,0,0,0,1];",
    "                vD=[0,0,0];",
    "                vC=[1,1,1];",
    "                vA=[1,1,1];",
    "            }",
    "            else{",
    "                vF=[2/3,0.5,0.02];",
    "                vB=[2/3,1,-1];",
    "            }",
    "            mG = matrix_scale2( mC, vect_mult(vA,vB) );",
    "            vH = vect_add( vect_add( matrix_vector_mult2(mG,vE), vect_mult(vA,vD) ), vF);",
    "            if (vertices[k][2*i].length!=0){",
    "                gl[k].useProgram(shaderProgram[k]);",
    "                gl[k].uniformMatrix3fv(M1[k],false,new Float32Array(mG));",
    "                gl[k].uniform3f(V1[k],vH[0],vH[1],vH[2]);",
    "                gl[k].bindBuffer(gl[k].ARRAY_BUFFER, vertex_buffer[k][2*i]);",
    "                gl[k].vertexAttribPointer(coord[k], 3, gl[k].FLOAT, false, 0, 0);",
    "                gl[k].enableVertexAttribArray(coord[k]);",
    "                gl[k].bindBuffer(gl[k].ARRAY_BUFFER, color_buffer[k][2*i]);",
    "                gl[k].vertexAttribPointer(color[k], 3, gl[k].UNSIGNED_BYTE, true, 0, 0);",
    "                gl[k].enableVertexAttribArray(color[k]);",
    "                gl[k].drawArrays(gl[k].TRIANGLES, 0, vertices[k][2*i].length/3);",
    "            }",
    "            if (i==3) vH[2] += 0.01;",
    "            else vH[2] += -0.01;",
    "            if (vertices[k][2*i+1].length!=0){",
    "                if (colors[k][2*i+1].length!=0){",
    "                    gl[k].useProgram(shaderProgram[k]);",
    "                    gl[k].uniformMatrix3fv(M1[k],false,new Float32Array(mG));",
    "                    gl[k].uniform3f(V1[k],vH[0],vH[1],vH[2]);",
    "                    gl[k].bindBuffer(gl[k].ARRAY_BUFFER, vertex_buffer[k][2*i+1]);",
    "                    gl[k].vertexAttribPointer(coord[k], 3, gl[k].FLOAT, false, 0, 0);",
    "                    gl[k].enableVertexAttribArray(coord[k]);",
    "                    gl[k].bindBuffer(gl[k].ARRAY_BUFFER, color_buffer[k][2*i+1]);",
    "                    gl[k].vertexAttribPointer(color[k], 3, gl[k].UNSIGNED_BYTE, true, 0, 0);",
    "                    gl[k].enableVertexAttribArray(color[k]);",
    "                    gl[k].drawArrays(gl[k].LINES, 0, vertices[k][2*i+1].length/3);",
    "                }",
    "                else{",
    "                    /* this shader only draws black */",
    "                    gl[k].useProgram(shaderProgram2[k]);",
    "                    gl[k].uniformMatrix3fv(M2[k],false,new Float32Array(mG));",
    "                    gl[k].uniform3f(V2[k],vH[0],vH[1],vH[2]);",
    "                    gl[k].bindBuffer(gl[k].ARRAY_BUFFER, vertex_buffer[k][2*i+1]);",
    "                    gl[k].vertexAttribPointer(coord2[k], 3, gl[k].FLOAT, false, 0, 0);",
    "                    gl[k].enableVertexAttribArray(coord2[k]);",
    "                    gl[k].drawArrays(gl[k].LINES, 0, vertices[k][2*i+1].length/3);",
    "                }",
    "            }",
    "        }",
    "        /* display how many triangles and lines were drawn */",
    "        var tri=(vertices[k][0].length+vertices[k][2].length+vertices[k][4].length+vertices[k][6].length+vertices[k][8].length)/9;",
    "        var lin=(vertices[k][1].length+vertices[k][3].length+vertices[k][5].length+vertices[k][7].length+vertices[k][9].length)/6;",
    "        document.getElementById('textD'+(k+3)).innerHTML = '&#160 '+tri+' tri, '+lin+' lin';",
    "        drawing[k] = 0;",
    "    }",
    "    function getobjectcount(k){",
    "        var count = 0;",
    "        for (var i=0;i<10;i++) count += vertices[k][i].length;",
    "        return count;",
    "    }",
    "    function resetposition(k){",
    "        /* reset WebGL object position */",
    "        rmatrix[k]=[1,0,0,0,1,0,0,0,1];",
    "        zoom[k]=1;",
    "        x_trans[k]=0;",
    "        y_trans[k]=0;",
    "        if (ikey==1) updateInfo();",
    "    }",
    "    function releasememory(k){",
    "        /* request server to free WebGL data and release locally */",
    "        if (webgl==0) return;",
    "        gl[k].clearColor(1.0, 1.0, 1.0, 1.0);",
    "        gl[k].enable(gl[k].DEPTH_TEST);",
    "        gl[k].clear(gl[k].COLOR_BUFFER_BIT);",
    "        gl[k].viewport(0, 0, canvas[k].width, canvas[k].height);",
    "        document.getElementById('textD'+(k+3)).innerHTML = '&#160 0 tri, 0 lin';",
    "        for (var j=0;j<10;j++){",
    "            vertices[k][j]=[];",
    "            colors[k][j]=[];",
    "        }",
    "        AJAX('callfunct.php','release='+(k+3),1,1,0,1);",
    "    }",
    "    function releasememory2(k){",
    "        /* request server to free image data and release locally */",
    "        if (webgl!=0){",
    "            document.getElementById('cdiv'+k).style.display='none';",
    "            document.getElementById('cdiv'+(k+3)).style.display='inline-block';",
    "        }",
    "        AJAX('callfunct.php','release='+k,1,1,0,1);",
    "        document.getElementById('figure'+k).src='figure'+k+'.bmp?'+Math.random();",
    "    }",
    "    function getHeight() {",
    "        /* get browser height */",
    "        var h=0;",
    "        if (self.innerHeight) h = self.innerHeight;",
    "        else if (document.documentElement && document.documentElement.clientHeight)",
    "            h = document.documentElement.clientHeight;",
    "        else if (document.body) h = document.body.clientHeight;",
    "        return h;",
    "    }",
    "    function getWidth(actual) {",
    "        /* get browser width/2 */",
    "        var w=0;",
    "        if (self.innerWidth) w = self.innerWidth;",
    "        else if (document.documentElement && document.documentElement.clientWidth)",
    "            w = document.documentElement.clientWidth;",
    "        else if (document.body) w = document.body.clientWidth;",
    "        if (wkey==-1) return w-50;",
    "        if (sg==1 && actual==0) {",
    "            w = w - 50;",
    "            var h = getHeight()-30;",
    "            h = 1.5 * h;",
    "            if (h<w && popped[0]*popped[1]*popped[2]==0) w = h;",
    "            return w;",
    "        }",
    "        return (w-50)/2;",
    "    }",
    "    function resizecanvas(){",
    "        /* rescale so 4 canvas fit in web browser */",
    "        var width = getWidth(0);",
    "        if (width<300) width=300;",
    "        height = width*2/3;",
    "        var doc1 = document.getElementById(\"controls\");",
    "        doc1.style.width = width;",
    "        doc1.style.height = height;",
    "        var factor = 800; if (isChrome) factor = 600;",
    "        document.getElementById(\"command\").size = 80 * width / factor;",
    "        if (firstresize==1){",
    "            firstresize=0;",
    "            for (var i=0;i<3;i++){",
    "                if (sg!=1 && getobjectcount(i)==0 && document.getElementById('figure'+i).height > 1){",
    "                    document.getElementById(\"cdiv\"+i).style.display = \"inline-block\";",
    "                    document.getElementById(\"cdiv\"+(i+3)).style.display = \"none\";",
    "                }",
    "            }",
    "        }",
    "        var h1 = document.getElementById(\"head\");",
    "        if (!h1 || h1.style.display=='none'){",
    "            var h2 = document.getElementById(\"head2\");",
    "            if (wkey==-1) h2.style.display='inline-block';",
    "            else h2.style.display='block';",
    "        }",
    "        for (var i=0;i<3;i++){",
    "            if (webgl!=0){",
    "                canvas[i].width = width;",
    "                canvas[i].height = height;",
    "            }",
    "            document.getElementById(\"cdiv\"+(i+3)).style.width = width;",
    "            document.getElementById('figure'+i).width = width;",
    "            document.getElementById('figure'+i).height = height;",
    "            document.getElementById(\"cdiv\"+i).style.width = width;",
    "            draw(i);",
    "        }",
    "        var w = 25;",
    "        if (width>600) w = width/20;",
    "        document.getElementById(\"confirmbutton\").style.fontSize = w;",
    "        var btndivs = document.getElementsByClassName(\"btn\");",
    "        for (var i=0;i<btndivs.length;i++){",
    "            btndivs[i].style.paddingRight = width / 60;",
    "            if (isSafari) btndivs[i].style.paddingRight = 0;",
    "            var btns = btndivs[i].getElementsByTagName(\"button\");",
    "            for (var j=0;j<btns.length;j++){",
    "                if (width>600) {",
    "                    btns[j].style.fontSize = width / 40;",
    "                    btns[j].style.color = \"#333333\";",
    "                    btns[j].style.borderRadius = \"10px\";",
    "                    btns[j].style.backgroundColor = \"#EEEEEE\";",
    "                    if (buttonColored(btns[j].id)==1) btns[j].style.backgroundColor = \"#999999\";",
    "                }",
    "                else {",
    "                    btns[j].style.fontSize = \"\";",
    "                    btns[j].style.color = \"\";",
    "                    btns[j].style.borderRadius = \"8px\";",
    "                    btns[j].style.backgroundColor = \"#EEEEEE\";",
    "                    if (buttonColored(btns[j].id)==1) btns[j].style.backgroundColor = \"#999999\";",
    "                }",
    "            }",
    "            ",
    "            var divs = document.getElementsByTagName(\"div\");",
    "            for (var j=0;j<divs.length;j++){",
    "                if (divs[j].id.indexOf(\"parameters\")!=-1 || divs[j].id.indexOf(\"options\")!=-1) {",
    "                    if (width>600) divs[j].style.fontSize = width / 35;",
    "                    else divs[j].style.fontSize = \"\";",
    "                    var descendants = divs[j].querySelectorAll(\"*\");",
    "                    for (var k=0;k<descendants.length;k++){",
    "                        if (width>600) {",
    "                            if (descendants[k].tagName==\"BUTTON\" || descendants[k].tagName==\"INPUT\")",
    "                                descendants[k].style.fontSize = width / 40;",
    "                            else descendants[k].style.fontSize = width / 35;",
    "                        }",
    "                        else descendants[k].style.fontSize = \"\";",
    "                    }",
    "                }",
    "            }",
    "            ",
    "        }",
    "        resizeframe();",
    "        if (ikey==1) updateInfo();",
    "        var t3 = document.getElementById(\"text3\");",
    "        if (width>600) {",
    "            document.getElementById(\"text\").contentDocument.body.style.fontSize = width / 35;",
    "            if (t3) t3.contentDocument.body.style.fontSize = width / 35;",
    "            document.getElementById(\"head2\").style.fontSize = width / 35;",
    "        }",
    "        else {",
    "            document.getElementById(\"text\").contentDocument.body.style.fontSize = \"\";",
    "            if (t3) t3.contentDocument.body.style.fontSize = \"\";",
    "            document.getElementById(\"head2\").style.fontSize = \"\";",
    "        }",
    "        if (animate<-1){",
    "            var map=[5,6,4];",
    "            animate = map[-animate-2];",
    "            reset = 1;",
    "        }",
    "        var txt = \"INTERACTIVE MODE: Frame rate = \"+(animate*10)+\" fps. Key and mouse presses sent to server.\";",
    "        if (animate==4) txt = \"INTERACTIVE MODE: Key and mouse presses sent to server.\";",
    "        if (animate==5) txt = \"INTERACTIVE MODE: Key presses sent to server.\";",
    "        if (animate==6) txt = \"INTERACTIVE MODE: Mouse presses sent to server.\";",
    "        if (animate>6) txt = \"ANIMATION MODE: Frame rate = \"+((animate-6)*10)+\" fps.\";",
    "        if (animate>0) document.getElementById(\"animate\").innerHTML = txt;",
    "        else document.getElementById(\"animate\").innerHTML=\"\";",
    "    }",
    "    function resizeframe(){",
    "        /* rescale out text frame */",
    "        var h1 = document.getElementById(\"head\");",
    "        var dy = document.getElementById(\"head2\").clientHeight;",
    "        if (h1 && h1.style.display!='none') dy = h1.clientHeight;",
    "        document.getElementById(\"text\").height=document.getElementById(\"controls\").clientHeight-dy;",
    "        document.getElementById(\"text\").width=document.getElementById(\"controls\").clientWidth-10;",
    "        var width = getWidth(0);",
    "        if (width<300) width=300;",
    "        var extra = 0;",
    "        if (isSafari) extra = 20;",
    "        document.getElementById(\"blackout\").style.height = dy + extra;",
    "        document.getElementById(\"blackout\").style.width = width;",
    "    }",
    "    function hide(k){",
    "        /* popping out a WebGL display */",
    "        document.getElementById(\"controls\").style.display = \"none\";",
    "        for (var i=0;i<3;i++){",
    "            document.getElementById(\"cdiv\"+i).style.display = \"none\";",
    "            if (i!=k) document.getElementById(\"cdiv\"+(i+3)).style.display = \"none\";",
    "        }",
    "        document.getElementById(\"pop\"+k).innerHTML = \"Push\";",
    "        document.getElementById(\"pop\"+k).onclick = function() { push(k); };",
    "    }",
    "    function unhide(k){",
    "        /* pushing a WebGL display into controls */",
    "        if (webgl!=0) document.getElementById(\"cdiv\"+(k+3)).style.display = \"inline-block\";",
    "        else document.getElementById(\"cdiv\"+k).style.display = \"inline-block\";",
    "        sg = -1;",
    "        resizecanvas();",
    "        if (popped[k]==2) AJAX2(k);",
    "        popped[k]=0;",
    "    }",
    "    function pop(k){",
    "        /* popping out a WebGL display */",
    "        window.open('sg?x='+k);",
    "        document.getElementById(\"cdiv\"+k).style.display = \"none\";",
    "        document.getElementById(\"cdiv\"+(k+3)).style.display = \"none\";",
    "        document.getElementById(\"filechoice\"+k).style.display = \"none\";",
    "        popped[k]=1;",
    "        if (popped[0]>0 && popped[1]>0 && popped[2]>0) {",
    "            sg = 1;",
    "            resizecanvas();",
    "        }",
    "    }",
    "    function save(k){",
    "        /* saving WebGL object as either gpu binary data or text */",
    "        if (optionkey==1) window.open('data'+k+'.js?xtra=1');",
    "        else window.open('data'+k+'.gpu');",
    "    }",
    "    function push(k){",
    "        /* popping out a WebGL display */",
    "        AJAX('callfunct.php','push='+k,1,1,0,1);",
    "        setTimeout(function(){window.close();},100);",
    "    }",
    "    function matrix_quaternion3(theta,x1,y1,x2,y2,k){",
    "        var x3 = x2-x1;",
    "        var y3 = y2-y1;",
    "        var d3 = Math.sqrt(x3*x3+y3*y3);",
    "        if (d3==0 || theta==0) return [1,0,0,0,1,0,0,0,1];",
    "        x3 = x3/d3;",
    "        y3 = y3/d3;",
    "        var dot = x2*x3+y2*y3;",
    "        var x4 = x2 - dot*x3;",
    "        var y4 = y2 - dot*y3;",
    "        var d4 = Math.sqrt(x4*x4+y4*y4);",
    "        var d5 = 0;",
    "        if (d4<1) d5 = Math.sqrt(1-d4*d4);",
    "        else d4 = 1;",
    "        var z = x2*y3-x3*y2;",
    "        old_d[k] = 1;",
    "        if (z>0) old_d[k] = -1;",
    "        var u = [d5*x4/d4,d5*y4/d4,-d4];",
    "        u = normalize(u);",
    "        old_u[k] = u;",
    "        return matrix_quaternion4(theta,u,old_d[k]);",
    "    }",
    "    function matrix_quaternion4(theta,u,d){",
    "        theta = theta*d;",
    "        var s = Math.sin(theta/2);",
    "        var qr = Math.cos(theta/2);",
    "        var qi = s*u[0];",
    "        var qj = s*u[1];",
    "        var qk = s*u[2];",
    "        var qi2 = qi*qi;",
    "        var qj2 = qj*qj;",
    "        var qk2 = qk*qk;",
    "        var qiqj = qi*qj;",
    "        var qkqr = qk*qr;",
    "        var qiqk = qi*qk;",
    "        var qjqr = qj*qr;",
    "        var qjqk = qj*qk;",
    "        var qiqr = qi*qr;",
    "        var result = [",
    "            1-2*(qj2+qk2), 2*(qiqj+qkqr), 2*(qiqk-qjqr),",
    "            2*(qiqj-qkqr), 1-2*(qi2+qk2), 2*(qjqk+qiqr),",
    "            2*(qiqk+qjqr), 2*(qjqk-qiqr), 1-2*(qi2+qj2)",
    "        ];",
    "        return result;",
    "    }",
    "    function normalize(x){",
    "        var s = Math.sqrt(x[0]*x[0]+x[1]*x[1]+x[2]*x[2]);",
    "        var result = [x[0]/s, x[1]/s, x[2]/s];",
    "        return result;",
    "    }",
    "    function matrix_matrix_mult(mx,ax){",
    "        var r1=[mx[0],mx[1],mx[2]];",
    "        var r2=[mx[3],mx[4],mx[5]];",
    "        var r3=[mx[6],mx[7],mx[8]];",
    "        var c1=[ax[0],ax[3],ax[6]];",
    "        var c2=[ax[1],ax[4],ax[7]];",
    "        var c3=[ax[2],ax[5],ax[8]];",
    "        var result=[dp(r1,c1), dp(r1,c2), dp(r1,c3), dp(r2,c1), dp(r2,c2), dp(r2,c3), dp(r3,c1), dp(r3,c2), dp(r3,c3)];",
    "        return result;",
    "    }",
    "    function matrix_vector_mult2(mx,x){",
    "    /* Left multiply 3x3 maxtrix mx by vector x */",
    "        var c1=[mx[0],mx[3],mx[6]];",
    "        var c2=[mx[1],mx[4],mx[7]];",
    "        var c3=[mx[2],mx[5],mx[8]];",
    "        var result=[dp(c1,x), dp(c2,x), dp(c3,x)];",
    "        return result;",
    "    }",
    "    function matrix_scale2(mx,x){",
    "        var result = [x[0]*mx[0], x[1]*mx[1], x[2]*mx[2], x[0]*mx[3], x[1]*mx[4], x[2]*mx[5], x[0]*mx[6], x[1]*mx[7], x[2]*mx[8]];",
    "        return result;",
    "    }",
    "    function vect_add(x,y){",
    "        var result = [x[0]+y[0], x[1]+y[1], x[2]+y[2]];",
    "        return result;",
    "    }",
    "    function vect_mult(x,y){",
    "        var result = [x[0]*y[0], x[1]*y[1], x[2]*y[2]];",
    "        return result;",
    "    }",
    "    function dp(x,y){",
    "    /* Calculate the dot product of R3 vectors x and y */",
    "        return x[0]*y[0]+x[1]*y[1]+x[2]*y[2];",
    "    }",
    "    function updateInfo(){",
    "        var mid = document.getElementById(\"mouseinfodiv\");",
    "        var k = focus;",
    "        var w = getWidth(0);",
    "        if (w<300) w=300;",
    "        var h = 2/3 * w + 30;",
    "        if (k==0 && sg!=1){",
    "            w = 2*w;",
    "            h = 0;",
    "        }",
    "        else if (k==2 && sg!=1) w = 2*w;",
    "        if (sg==1) {",
    "            h=0;",
    "            w = 2 * getWidth(1);",
    "        }",
    "        var x = 1.5 * x_trans[k]/canvas[k].width;",
    "        var y = -y_trans[k]/canvas[k].height;",
    "        var txt = \"<u>Pane \"+focus+\" info:</u><br><br>\";",
    "        txt += \"zoom = \"+zoom[k].toFixed(2)+\"<br><br>\";",
    "        var p = Math.floor(Math.log(zoom[k])/2.3)+2;",
    "        txt += \"x shift = \"+x.toFixed(p)+\"<br><br>\";",
    "        txt += \"y shift = \"+y.toFixed(p)+\"<br><br>\";",
    "        txt += \"rotation matrix = <br>\";;",
    "        txt += \"<table>\";",
    "        txt += \"<tr><td>\"+rmatrix[k][0].toFixed(2)+\"</td><td>\"+rmatrix[k][1].toFixed(2)+\"</td><td>\"+rmatrix[k][2].toFixed(2)+\"</td></tr>\";",
    "        txt += \"<tr><td>\"+rmatrix[k][3].toFixed(2)+\"</td><td>\"+rmatrix[k][4].toFixed(2)+\"</td><td>\"+rmatrix[k][5].toFixed(2)+\"</td></tr>\";",
    "        txt += \"<tr><td>\"+rmatrix[k][6].toFixed(2)+\"</td><td>\"+rmatrix[k][7].toFixed(2)+\"</td><td>\"+rmatrix[k][8].toFixed(2)+\"</td></tr>\";",
    "        txt += \"</table>\";",
    "        mid.innerHTML = txt;",
    "        mid.style.left = w - 100;",
    "        mid.style.top = h + 20;",
    "        mid.style.display = \"inline-block\";",
    "    }",
    "    function setAnimate(){",
    "        var extra = '';",
    "        if (sg==1) extra = '?x='+pane;",
    "        if (animate>0) {",
    "            document.getElementById('animate').innerHTML=\"INTERACTIVE MODE\";",
    "            if (timerId!=0){",
    "                clearInterval(timerId);",
    "                var txt = \"INTERACTIVE MODE: \";",
    "                var txt2 = \"Key and mouse presses sent to server.\";",
    "                var fps = \"Frame rate = 10 fps. \"; var callrate=100;",
    "                if (animate==2 || animate==8){fps = \"Frame rate = 20 fps. \"; callrate=50;}",
    "                else if (animate==3 || animate==9){fps = \"Frame rate = 30 fps. \"; callrate=33;}",
    "                else if (animate==4){fps = \"\"; callrate=500;}",
    "                else if (animate==5){fps = \"\"; callrate=500; txt2 = \"Key presses sent to server.\";}",
    "                else if (animate==6){fps = \"\"; callrate=500; txt2 = \"Mouse presses sent to server.\";}",
    "                timerId = setInterval(\"AJAX('readline.php\"+extra+\"','',1,1,0,0)\",callrate);",
    "                if (animate>=7 && animate<=9) {txt=\"ANIMATION MODE: \"; txt2=\"\";}",
    "                document.getElementById('animate').innerHTML=txt+fps+txt2;",
    "            }",
    "        }",
    "        else {",
    "            document.getElementById('animate').innerHTML=\"\";",
    "            if (timerId!=0){",
    "                clearInterval(timerId);",
    "                timerId = setInterval(\"AJAX('readline.php\"+extra+\"','',1,1,0,0)\",500);",
    "            }",
    "        }",
    "        if (animate<=0 || animate>=6) document.getElementById('lastkey').innerHTML=\"\";",
    "        if (animate<=0 || animate==5 || animate>=7) document.getElementById('lastmse').innerHTML=\"\";",
    "    }",
    "    function keyDown(e){",
    "        var key = e.keyCode;",
    "        if (animate>0 && animate<=5 && document.activeElement.tagName!=\"INPUT\") {",
    "            AJAX('writeline.php',\"cmd='key code=\"+key+\"'\",1,1,0,1);",
    "            document.getElementById('lastkey').innerHTML = \"(last pressed key: code = \"+key+\")\";",
    "            var extra = ''; if (sg==1) extra = '?x='+pane;",
    "            if (animate!=2 && animate!=3) setTimeout(\"AJAX('readline.php\"+extra+\"','',1,1,0,0)\",20);",
    "        }",
    "        if (key==67 && optionkey){ //c-key",
    "            var h1 = document.getElementById(\"head\");",
    "            if (!h1) return;",
    "            var h2 = document.getElementById(\"head2\");",
    "            if (h1.style.display=='none'){",
    "                h1.style.display='inline-block';",
    "                h2.style.display='none';",
    "                AJAX('callfunct.php','query=1',1,1,0,1);",
    "            }",
    "            else{",
    "                if (closeall()==-1) return;",
    "                h1.style.display='none';",
    "                h2.style.display='inline-block';",
    "                AJAX('callfunct.php','query=0',1,1,0,1);",
    "            }",
    "            resizecanvas();",
    "        }",
    "        else if (key==73 && optionkey && webgl==1) { //i-key",
    "            ikey *= -1;",
    "            if (ikey==1) updateInfo();",
    "            else document.getElementById(\"mouseinfodiv\").style.display = \"none\";",
    "        }",
    "        else if (key==87 && optionkey) { //w-key",
    "            wkey *= -1;",
    "            resizecanvas();",
    "        }",
    "        else if (key==82 && optionkey) { //r-key",
    "            if (animate==0) {animate=-1; reset=0; alert('Now new WebGL objects will NOT reset position.'); }",
    "            else if (reset==1) {reset=0; alert('Now new WebGL objects will NOT reset position.'); }",
    "            else if (animate==-1) {animate=0; reset=1; alert('Now new WebGL objects WILL reset position.'); }",
    "            else if (animate>=4 && animate<=6) {reset=1; alert('Now new WebGL objects WILL reset position.'); }",
    "        }",
    "        else if (key==80 && optionkey) pkey = 1; //p-key",
    "        else if (key>=48 && key<=57 && optionkey && pkey==1){ //0,1,2,3,4,5,6,7,8,9-key",
    "            animate = key-48;",
    "            var codes = [0,5,6,4,1,2,3,7,8,9];",
    "            animate = codes[animate];",
    "            AJAX('callfunct.php','animate='+animate,1,1,0,1);",
    "            setAnimate();",
    "        }",
    "        else if (key==70 && optionkey){ //f-key",
    "            fkey *= -1;",
    "            AJAX('callfunct.php','firewall='+(fkey+1),1,1,0,1);",
    "            if (fkey==1) document.getElementById('locked').innerHTML = \"FIREWALL ON: Only your ip address can access webgui.\";",
    "            else document.getElementById('locked').innerHTML = \"\";",
    "        }",
    "        else if (key==69 && optionkey && webgl==1){ //e-key",
    "            ekey *= -1;",
    "            AJAX('callfunct.php','endian='+(ekey+1),1,1,0,1);",
    "            if (ekey==1) document.getElementById('endian').style.display=\"block\";",
    "            else document.getElementById('endian').style.display=\"none\";",
    "        }",
    "        else if (key==18) optionkey = 1;",
    "        else if (key==91 || key==93 || key==224) commandkey = 1;",
    "        if (key!=80 && key!=18 && optionkey==1) pkey = -1;",
    "    }",
    "    function lockip(argv){",
    "        var ip = \"(\"+argv[1]+\".\"+argv[2]+\".\"+argv[3]+\".\"+argv[4]+\")\";",
    "        if (fkey==1) document.getElementById('locked').innerHTML = \"FIREWALL ON: Only your ip address \"+ip+\" can access webgui.\";",
    "        else document.getElementById('locked').innerHTML = \"\";",
    "    }",
    "    function keyUp(e){",
    "        var key = e.keyCode;",
    "        if (key==67 || key==73 || key==70 || key==69 || (key>=48 && key<=57) || key==87 || key==80 || key==82) return;",
    "        optionkey = 0;",
    "        commandkey = 0;",
    "    }",
    "    function mouseDown2(e){",
    "        if (animate>0 && animate!=5 && animate<7) {",
    "            var k = parseInt(e.target.id[6])+3;",
    "            var button = e.button;",
    "            if (optionkey==1) button=1;",
    "            if (commandkey==1) button=2;",
    "            var rect = e.target.getBoundingClientRect();",
    "            var x = (e.clientX - rect.left)/rect.height;",
    "            var y = 1-(e.clientY - rect.top)/rect.height;",
    "            var temp = button+\", x = \"+x.toFixed(6)+\", y = \"+y.toFixed(6);",
    "            AJAX('writeline.php',\"cmd='mse button=\"+button+\",x=\"+x.toFixed(6)+\",y=\"+y.toFixed(6)+\",pane=\"+k+\"'\",1,1,0,1);",
    "            document.getElementById('lastmse').innerHTML = \"(last pressed mouse: button = \"+temp+\", pane = \"+k+\")\";",
    "            var extra = ''; if (sg==1) extra = '?x='+pane;",
    "            if (animate!=2 && animate!=3) setTimeout(\"AJAX('readline.php\"+extra+\"','',1,1,0,0)\",20);",
    "        }",
    "        e.preventDefault();",
    "        return false;",
    "    }",
    "    function mouseDown(e){",
    "        var k = parseInt(e.target.id[9]);",
    "        if (isNaN(k) || k<0 || k>2) return false;",
    "        focus = k;",
    "        if (ikey==1) updateInfo();",
    "        btnfix = e.button;",
    "        drag[k] = 1;",
    "        old_x[k] = e.pageX;",
    "        old_y[k] = e.pageY;",
    "        old2_x[k] = e.pageX;",
    "        old2_y[k] = e.pageY;",
    "        rmatrix_old[k] = rmatrix[k];",
    "        var rect = e.target.getBoundingClientRect();",
    "        var xpix = e.clientX - rect.left - x_trans[k]*zoom[k];",
    "        var ypix = e.clientY - rect.top - y_trans[k]*zoom[k];",
    "        var x = 2*(1.5*xpix/canvas[k].width - 0.5)/zoom[k];",
    "        var y = 2*(1 - ypix/canvas[k].height - 0.5)/zoom[k];",
    "        old3_x[k] = x;",
    "        old3_y[k] = y;",
    "        if ((vertices[k][0]==0 && vertices[k][1]==0) && animate>0 && animate!=5 && animate<7)",
    "            sendmouse(e,k);",
    "        e.preventDefault();",
    "        return false;",
    "    }",
    "    function mouseUp(e){",
    "        var k = parseInt(e.target.id[9]);",
    "        if (isNaN(k) || k<0 || k>2) return false;",
    "        drag[k] = -1;",
    "        if (e.pageX==old2_x[k] && e.pageY==old2_y[k]){",
    "            old_dx[k] = 0;",
    "            old_dy[k] = 0;",
    "        }",
    "        if (Math.abs(e.pageX-old2_x[k])+Math.abs(e.pageY-old2_y[k])<10)",
    "            if ((vertices[k][0]!=0 || vertices[k][1]!=0) && animate>0 && animate!=5 && animate<7)",
    "                sendmouse(e,k);",
    "        e.preventDefault();",
    "        return false;",
    "    }",
    "    function sendmouse(e,k){",
    "        var det = rmatrix[k][0]*rmatrix[k][4]-rmatrix[k][1]*rmatrix[k][3];",
    "        if (det==0) return;",
    "        var rect = e.target.getBoundingClientRect();",
    "        var xpix = e.clientX - rect.left;",
    "        var ypix = e.clientY - rect.top;",
    "        var xx = 2*(1.5*xpix/canvas[k].width - 0.5);",
    "        var yy = 2*(1 - ypix/canvas[k].height - 0.5);",
    "        var xt = 2 * 1.5 * x_trans[k]/canvas[k].width;",
    "        var yt = 2 * -y_trans[k]/canvas[k].height;",
    "        xx=(xx-zoom[k]*xt)/zoom[k];",
    "        yy=(yy-zoom[k]*yt)/zoom[k];",
    "        var m = [rmatrix[k][4]/det, -rmatrix[k][3]/det, -rmatrix[k][1]/det, rmatrix[k][0]/det];",
    "        var x=xx*m[0]+yy*m[1];",
    "        var y=xx*m[2]+yy*m[3];",
    "        var button = e.button;",
    "        if (optionkey==1) button=1;",
    "        if (commandkey==1) button=2;",
    "        var temp = button+\", x = \"+x.toFixed(6)+\", y = \"+y.toFixed(6);",
    "        AJAX('writeline.php',\"cmd='mse button=\"+button+\",x=\"+x.toFixed(6)+\",y=\"+y.toFixed(6)+\",pane=\"+k+\"'\",1,1,0,1);",
    "        document.getElementById('lastmse').innerHTML = \"(last pressed mouse: button = \"+temp+\", pane = \"+k+\")\";",
    "        var extra = ''; if (sg==1) extra = '?x='+pane;",
    "        if (animate!=2 && animate!=3) setTimeout(\"AJAX('readline.php\"+extra+\"','',1,1,0,0)\",20);",
    "    }",
    "    function spin(k){",
    "        var timestamp = Date.now();",
    "        var inc = 0.001;",
    "        if (stopspin[k]==1 || getobjectcount(k)==0) {",
    "            oldtimestamp[k] = 0;",
    "            drawing[k] = 0;",
    "            document.getElementById('spin'+k).innerHTML=\"Spin\";",
    "            return;",
    "        }",
    "        if (oldtimestamp[k]!=0 && drag[k]!=1) {",
    "            inc = (timestamp - oldtimestamp[k])/10000;",
    "            var d = inc * Math.sqrt(old_dx[k]*old_dx[k]+old_dy[k]*old_dy[k]);",
    "            var qmatrix = matrix_quaternion4(d,old_u[k],old_d[k]);",
    "            rmatrix[k] = matrix_matrix_mult(rmatrix[k],qmatrix);",
    "            if (ikey==1) updateInfo();",
    "            if (drawing[k]!=1 && (old_dx[k]!=0 || old_dy[k]!=0)) {",
    "                window.requestAnimationFrame( function() {draw(k);} );",
    "                drawing[k] = 1;",
    "                oldtimestamp[k] = Date.now();",
    "            }",
    "        }",
    "        else {",
    "            if (oldtimestamp[k]==0) document.getElementById('spin'+k).innerHTML=\"Stop\";",
    "            oldtimestamp[k] = Date.now();",
    "        }",
    "        setTimeout(function(){spin(k);},20);",
    "    }",
    "    function mouseMove(e){",
    "        var k = parseInt(e.target.id[9]);",
    "        if (isNaN(k) || k<0 || k>2 || (vertices[k][0]==0 && vertices[k][1]==0)) return false;",
    "        var dx = e.pageX - old_x[k];",
    "        var dy = e.pageY - old_y[k];",
    "        if (drag[k] == -1 && isMobile==0) return false;",
    "        var btn = e.button;",
    "        if (isChrome) btn = btnfix;",
    "        if (btn==1 || optionkey==1){",
    "            x_trans[k] = x_trans[k] + dx/zoom[k];",
    "            y_trans[k] = y_trans[k] + dy/zoom[k];",
    "        }",
    "        else if (btn==2 || commandkey==1)",
    "            zoom[k] = zoom[k] * (1.0 + (dx - dy)/canvas[k].height);",
    "        else if (btn==0){",
    "            old_dx[k] = 3.0*dx/zoom[k];",
    "            old_dy[k] = -3.0*dy/zoom[k];",
    "            var rect = e.target.getBoundingClientRect();",
    "            var xpix = e.clientX - rect.left - x_trans[k]*zoom[k];",
    "            var ypix = e.clientY - rect.top - y_trans[k]*zoom[k];",
    "            var x = 2*(1.5*xpix/canvas[k].width - 0.5)/zoom[k];",
    "            var y = 2*(1 - ypix/canvas[k].height - 0.5)/zoom[k];",
    "            var dx2 = e.pageX - old2_x[k];",
    "            var dy2 = e.pageY - old2_y[k];",
    "            var d = Math.sqrt(dx2*dx2+dy2*dy2);",
    "            var qmatrix = matrix_quaternion3(3.0*d/canvas[k].height/zoom[k],old3_x[k],old3_y[k],x,y,k);",
    "            rmatrix[k] = matrix_matrix_mult(rmatrix_old[k],qmatrix);",
    "        }",
    "        old_x[k] = e.pageX;",
    "        old_y[k] = e.pageY;",
    "        if (vertices[k][0].length + vertices[k][1].length !=0) {",
    "            if (ikey==1) updateInfo();",
    "            if (drawing[k]!=1) {",
    "                window.requestAnimationFrame( function() {draw(k);} );",
    "                drawing[k] = 1;",
    "            }",
    "        }",
    "        e.preventDefault();",
    "        return false;",
    "    }",
    "    function checkMobile(){",
    "        if( navigator.userAgent.match(/Android/i)",
    "         || navigator.userAgent.match(/webOS/i)",
    "         || navigator.userAgent.match(/iPhone/i)",
    "         || navigator.userAgent.match(/iPad/i)",
    "         || navigator.userAgent.match(/iPod/i)",
    "         || navigator.userAgent.match(/BlackBerry/i)",
    "         || navigator.userAgent.match(/Windows Phone/i)) isMobile=1;",
    "    }",
    "    function contextMenu(e){",
    "        if (e.button === 2) {",
    "            e.preventDefault();",
    "            return false;",
    "        }",
    "    }"
};

/**********************************************************************/
/*        WEBGUI A web browser based graphical user interface         */
/*                                                                    */
/*        Author: Christopher Deotte                                  */
/*                                                                    */
/*        Version: 1.0 - June 25, 2017                                */
/**********************************************************************/
void updatewebpageC(){
    /* creates part 3 of 4 for index.html and sg for web browser */
    int i, s=0, sl=0, clines=1438;
    for (i=0;i<clines;i++) s = s + strlen(indexChtml[i]) + 1;
    webpageC = (char*)malloc(s+1);
    webpageC[0] = '\0';
    for (i=0;i<clines;i++) sl += sprintf(webpageC+sl,"%s\n",indexChtml[i]);
    webpageC[s+1]='\0';
}
