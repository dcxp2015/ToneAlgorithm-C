#define _CRT_SECURE_NO_DEPRECATE

#define maxLength 75 // Arbitrary value

// m and n are hardcoded for now
#define m 3
#define n 1197

#define SIGN(a,b) ((b) > 0.0 ? fabs(a) : - fabs(a))

static double maxarg1, maxarg2;
#define FMAX(a,b) (maxarg1 = (a),maxarg2 = (b),(maxarg1) > (maxarg2) ? (maxarg1) : (maxarg2))

static int iminarg1, iminarg2;
#define IMIN(a,b) (iminarg1 = (a),iminarg2 = (b),(iminarg1 < (iminarg2) ? (iminarg1) : iminarg2))

static double sqrarg;
#define SQR(a) ((sqrarg = (a)) == 0.0 ? 0.0 : sqrarg * sqrarg)

int svdcmp(double **a, int nRows, int nCols, double *w, double **v);

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>


typedef struct Point{
	double x;
	double y;
	double z;
}Point;

typedef struct Vector{
	double dx;
	double dy;
	double dz;
}Vector;

typedef struct Plane{
	Vector u;
	Vector v;
	Point point;
	Vector normal;	
}Plane;

typedef struct newCoord{
	double u;
	double v;
}newCoord;

double distanceToPlane(Point point, Plane plane);
double determinant(Vector v1, Vector v2, Vector v3);
double dotProduct(Vector v1, Vector v2);
double magnitude(Vector v);
Vector getVectorFromPoints(Point p1, Point p2);

// prints an arbitrary size matrix to the standard output
void printMatrix(double **a, int rows, int cols);
void printMatrix(double **a, int rows, int cols) {
	int i, j;

	for (i = 0; i<rows; i++) {
		for (j = 0; j<cols; j++) {
			printf("%.4lf ", a[i][j]);
		}
		printf("\n");
	}
	printf("\n");
}

// prints an arbitrary size vector to the standard output
void printVector(double *v, int size);
void printVector(double *v, int size) {
	int i;

	for (i = 0; i<size; i++) {
		printf("%.4lf ", v[i]);
	}
	printf("\n\n");
}

// calculates sqrt( a^2 + b^2 ) with decent precision
double pythag(double a, double b);
double pythag(double a, double b) {
	double absa, absb;

	absa = fabs(a);
	absb = fabs(b);

	if (absa > absb)
		return(absa * sqrt(1.0 + SQR(absb / absa)));
	else
		return(absb == 0.0 ? 0.0 : absb * sqrt(1.0 + SQR(absa / absb)));
}

/*
Modified from Numerical Recipes in C
Given a matrix a[nRows][nCols], svdcmp() computes its singular value
decomposition, A = U * W * Vt.  A is replaced by U when svdcmp
returns.  The diagonal matrix W is output as a vector w[nCols].
V (not V transpose) is output as the matrix V[nCols][nCols].
*/

int svdcmp(double **a, int nRows, int nCols, double *w, double **v) {
	int flag, i, its, j, jj, k, l, nm;
	double anorm, c, f, g, h, s, scale, x, y, z, *rv1;

	rv1 = malloc(sizeof(double)*nCols);
	if (rv1 == NULL) {
		printf("svdcmp(): Unable to allocate vector\n");
		return(-1);
	}

	g = scale = anorm = 0.0;
	for (i = 0; i<nCols; i++) {
		l = i + 1;
		rv1[i] = scale*g;
		g = s = scale = 0.0;
		if (i < nRows) {
			for (k = i; k<nRows; k++) scale += fabs(a[k][i]);
			if (scale) {
				for (k = i; k<nRows; k++) {
					a[k][i] /= scale;
					s += a[k][i] * a[k][i];
				}
				f = a[i][i];
				g = -SIGN(sqrt(s), f);
				h = f * g - s;
				a[i][i] = f - g;
				for (j = l; j<nCols; j++) {
					for (s = 0.0, k = i; k<nRows; k++) s += a[k][i] * a[k][j];
					f = s / h;
					for (k = i; k<nRows; k++) a[k][j] += f * a[k][i];
				}
				for (k = i; k<nRows; k++) a[k][i] *= scale;
			}
		}
		w[i] = scale * g;
		g = s = scale = 0.0;
		if (i < nRows && i != nCols - 1) {
			for (k = l; k<nCols; k++) scale += fabs(a[i][k]);
			if (scale)  {
				for (k = l; k<nCols; k++) {
					a[i][k] /= scale;
					s += a[i][k] * a[i][k];
				}
				f = a[i][l];
				g = -SIGN(sqrt(s), f);
				h = f * g - s;
				a[i][l] = f - g;
				for (k = l; k<nCols; k++) rv1[k] = a[i][k] / h;
				for (j = l; j<nRows; j++) {
					for (s = 0.0, k = l; k<nCols; k++) s += a[j][k] * a[i][k];
					for (k = l; k<nCols; k++) a[j][k] += s * rv1[k];
				}
				for (k = l; k<nCols; k++) a[i][k] *= scale;
			}
		}
		anorm = FMAX(anorm, (fabs(w[i]) + fabs(rv1[i])));

		printf(".");
		fflush(stdout);
	}

	for (i = nCols - 1; i >= 0; i--) {
		if (i < nCols - 1) {
			if (g) {
				for (j = l; j<nCols; j++)
					v[j][i] = (a[i][j] / a[i][l]) / g;
				for (j = l; j<nCols; j++) {
					for (s = 0.0, k = l; k<nCols; k++) s += a[i][k] * v[k][j];
					for (k = l; k<nCols; k++) v[k][j] += s * v[k][i];
				}
			}
			for (j = l; j<nCols; j++) v[i][j] = v[j][i] = 0.0;
		}
		v[i][i] = 1.0;
		g = rv1[i];
		l = i;
		printf(".");
		fflush(stdout);
	}

	for (i = IMIN(nRows, nCols) - 1; i >= 0; i--) {
		l = i + 1;
		g = w[i];
		for (j = l; j<nCols; j++) a[i][j] = 0.0;
		if (g) {
			g = 1.0 / g;
			for (j = l; j<nCols; j++) {
				for (s = 0.0, k = l; k<nRows; k++) s += a[k][i] * a[k][j];
				f = (s / a[i][i]) * g;
				for (k = i; k<nRows; k++) a[k][j] += f * a[k][i];
			}
			for (j = i; j<nRows; j++) a[j][i] *= g;
		}
		else
			for (j = i; j<nRows; j++) a[j][i] = 0.0;
		++a[i][i];
		printf(".");
		fflush(stdout);
	}

	for (k = nCols - 1; k >= 0; k--) {
		for (its = 0; its<30; its++) {
			flag = 1;
			for (l = k; l >= 0; l--) {
				nm = l - 1;
				if ((fabs(rv1[l]) + anorm) == anorm) {
					flag = 0;
					break;
				}
				if ((fabs(w[nm]) + anorm) == anorm) break;
			}
			if (flag) {
				c = 0.0;
				s = 1.0;
				for (i = l; i <= k; i++) {
					f = s * rv1[i];
					rv1[i] = c * rv1[i];
					if ((fabs(f) + anorm) == anorm) break;
					g = w[i];
					h = pythag(f, g);
					w[i] = h;
					h = 1.0 / h;
					c = g * h;
					s = -f * h;
					for (j = 0; j<nRows; j++) {
						y = a[j][nm];
						z = a[j][i];
						a[j][nm] = y * c + z * s;
						a[j][i] = z * c - y * s;
					}
				}
			}
			z = w[k];
			if (l == k) {
				if (z < 0.0) {
					w[k] = -z;
					for (j = 0; j<nCols; j++) v[j][k] = -v[j][k];
				}
				break;
			}
			if (its == 29) printf("no convergence in 30 svdcmp iterations\n");
			x = w[l];
			nm = k - 1;
			y = w[nm];
			g = rv1[nm];
			h = rv1[k];
			f = ((y - z) * (y + z) + (g - h) * (g + h)) / (2.0 * h * y);
			g = pythag(f, 1.0);
			f = ((x - z) * (x + z) + h * ((y / (f + SIGN(g, f))) - h)) / x;
			c = s = 1.0;
			for (j = l; j <= nm; j++) {
				i = j + 1;
				g = rv1[i];
				y = w[i];
				h = s * g;
				g = c * g;
				z = pythag(f, h);
				rv1[j] = z;
				c = f / z;
				s = h / z;
				f = x * c + g * s;
				g = g * c - x * s;
				h = y * s;
				y *= c;
				for (jj = 0; jj<nCols; jj++) {
					x = v[jj][j];
					z = v[jj][i];
					v[jj][j] = x * c + z * s;
					v[jj][i] = z * c - x * s;
				}
				z = pythag(f, h);
				w[j] = z;
				if (z) {
					z = 1.0 / z;
					c = f * z;
					s = h * z;
				}
				f = c * g + s * y;
				x = c * y - s * g;
				for (jj = 0; jj < nRows; jj++) {
					y = a[jj][j];
					z = a[jj][i];
					a[jj][j] = y * c + z * s;
					a[jj][i] = z * c - y * s;
				}
			}
			rv1[l] = 0.0;
			rv1[k] = f;
			w[k] = x;
		}
		printf(".");
		fflush(stdout);
	}
	printf("\n");

	free(rv1);

	return(0);
}

Point getPointOnPlane(Point point, Plane plane){
	Point pointOnPlane;

	double dist = distanceToPlane(point, plane);
	Vector normal = plane.normal;

	Vector v;
	v.dx = dist*normal.dx;
	v.dy = dist*normal.dy;
	v.dz = dist*normal.dz;

	pointOnPlane.x = point.x - v.dx;
	pointOnPlane.y = point.y - v.dy;
	pointOnPlane.z = point.z - v.dz;

	return pointOnPlane;
}

double distanceToPlane(Point point, Plane plane){
	double dist;

	Vector v = getVectorFromPoints(point, plane.point);
	Vector normal = plane.normal;

	dist = (fabs(dotProduct(normal, v)) / magnitude(normal));

	return dist;
}

Point intersectionOfThreeVectors(Vector v1, Vector v2, Vector v3){
	Point intersect = { 1, 1, 1 };
	// Code goes here
	// Going to write my own implementation of the determinant/cross product
	
	// Create the vectors with 0s in the corresponding columns then do Cramer's Rule
	Vector case1col0 = { 0, v1.dy, v1.dz };
	Vector case1col1 = { 0, v2.dy, v2.dz };
	Vector case1col2 = { 0, v3.dy, v3.dz };

	Vector case2col0 = { v1.dx, 0, v1.dz };
	Vector case2col1 = { v2.dx, 0, v2.dz };
	Vector case2col2 = { v3.dx, 0, v3.dz };

	Vector case3col0 = { v1.dx, v1.dy, 0 };
	Vector case3col1 = { v2.dx, v2.dy, 0 };
	Vector case3col2 = { v3.dx, v3.dy, 0 };

	double botDet = determinant(v1, v2, v3);
	double case1Det = determinant(case1col0, case1col1, case1col2);
	double case2Det = determinant(case2col0, case2col1, case2col2);
	double case3Det = determinant(case3col0, case3col1, case3col2);

	double xCoord = case1Det / botDet;
	double yCoord = case2Det / botDet;
	double zCoord = case3Det / botDet;

	intersect = { xCoord, yCoord, zCoord };

	return intersect;
}

double determinant(Vector v1, Vector v2, Vector v3){
	double det;

	double val1 = v1.dx*(v2.dy*v3.dz - v2.dz*v3.dy);
	double val2 = v1.dy*(v2.dx*v3.dz - v2.dz*v3.dx);
	double val3 = v1.dz*(v2.dx*v3.dy - v2.dy*v3.dx);

	det = val1 - val2 + val3;

	return det;
}

double dotProduct(Vector v1, Vector v2){
	return v1.dx*v2.dx + v1.dy*v2.dy + v1.dz*v2.dz;
}

double magnitude(Vector v){
	return sqrt(v.dx*v.dx + v.dy*v.dy + v.dz*v.dz);
}

Vector unitVector(Vector v){
	Vector unitV;
	double mag = magnitude(v);

	unitV.dx = v.dx / mag;
	unitV.dy = v.dy / mag;
	unitV.dz = v.dz / mag;

	return unitV;
}

Vector getVectorFromPoints(Point p1, Point p2){
	Vector v;

	v.dx = p2.x - p1.x;
	v.dy = p2.y - p1.y;
	v.dz = p2.z - p1.z;

	return v;
}

newCoord rref(Point pointOnPlane, Plane plane){
	newCoord uvCoord;
	// Code goes here
	// Create matrix
	double mat[2][3];
	
	// Initialize variables
	double a11 = plane.u.dx;
	double a12 = plane.v.dx;
	double a13 = pointOnPlane.x;
	double a21 = plane.u.dy;
	double a22 = plane.v.dy;
	double a23 = pointOnPlane.y;

	// Fill in the matrix
	mat[0][0] = a11;
	mat[0][1] = a12;
	mat[0][2] = a13;
	mat[1][0] = a21;
	mat[1][1] = a22;
	mat[1][2] = a23;

	// Divide to make first column 
	mat[0][0] = a11 / a11;
	mat[0][1] = a12 / a11;
	mat[0][2] = a13 / a11;
	mat[1][0] = a21 / a21;
	mat[1][1] = a22 / a21;
	mat[1][2] = a23 / a21;

	// Subtract Row1 from Row2
	mat[1][0] = mat[1][0] - mat[0][0];
	mat[1][1] = mat[1][1] - mat[0][1];
	mat[1][2] = mat[1][2] - mat[0][2];

	// Divide second row to get a22 to be 1
	double temp = mat[1][1];
	mat[1][1] = mat[1][1] - temp;
	mat[1][2] = mat[1][2] - temp;

	// Subtract Row2 from Row1
	temp = mat[0][1];
	mat[0][2] = mat[0][2] - temp*mat[1][2];

	uvCoord.u = mat[0][2];
	uvCoord.v = mat[1][2];

	return uvCoord;
}

int main()
{
	// Load: time, a.x, a.y, a.z from raw_data.csv
	

	// Initialize variables
	double timestamp, acceleration_x, acceleration_y, acceleration_z = 0;
	int numLines = 0;


	// Create file pointer
	FILE *fp;


	// Open stream to count lines in file
	fp = fopen("raw_data.csv", "r");
	int ch;
	while (!feof(fp)){
		ch = fgetc(fp);
		if (ch == '\n'){
			numLines ++;
		}
	}
	numLines ++;
	fclose(fp);

	// Allocate space for array of times
	// double *timeArray = malloc(sizeof(double) * numLines);
	// Allocate space for array of acceleration
	// double *accelerationArray = malloc(sizeof(double) * numLines * 3);

	double timeArray[n];
	double xyzAccelerationArray[m][n][3];



	// Open stream to read the data
	fp = fopen("raw_data.csv", "r");

	char string[maxLength];
	char* str;

	int counter = 0;
	int row;
	int col;

	while (fgets(string, maxLength, fp)) {
		// Remove trailing \n
		size_t ln = strlen(string) - 1;
		if (string[ln] == '\n'){
			string[ln] = '\0';
		}

		// Split the string by comma
		str = _strdup(string);
		char *element1 = strtok(str, ",");
		char *element2 = strtok(NULL, ",");
		str = _strdup(NULL);
		char *element3 = strtok(str, ",");
		char *element4 = strtok(NULL, ",");


		// Change strings to doubles
		timestamp = atof(element1);
		acceleration_x = atof(element2);
		acceleration_y = atof(element3);
		acceleration_z = atof(element4);


		// Store timestamps
		timeArray[counter] = timestamp;

		row = counter / n;
		col = counter % n;

		// Store acceleration 
		xyzAccelerationArray[row][col][0] = acceleration_x;
		xyzAccelerationArray[row][col][1] = acceleration_y;
		xyzAccelerationArray[row][col][2] = acceleration_z;

		// printf("%s %s %s %s\n", element1, element2, element3, element4);
		// printf("%f %f %f %f\n", timestamp, acceleration_x, acceleration_y, acceleration_z);
		
		// printf("%s\n", string);
		counter ++;
	}

	fclose(fp);
	// End read from file

	// Run Singular Variable Decomposition
	double uMatrix[3][3];
	double vMatrix[3][3];
	svdcmp(xyzAccelerationArray, 3, numLines, uMatrix, vMatrix);

	// Get U and S

	// Find intersection of vectors (0, 0, 0)

	// Create plane

	// Put points on to plane

	// Find linear combination (rref)

	// Return data

	printf("\n");
	printf("numLines: %d\n", numLines);

	printf("end of file \n");

	// printf("%f", timeArray[0]);

	getchar();
	return 0;
}